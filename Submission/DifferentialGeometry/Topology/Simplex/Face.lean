import Mathlib.Analysis.Convex.StdSimplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Simplex


def face {n : ℕ} (i : Fin (n + 2)) : Set (stdSimplex ℝ (Fin (n + 2))) :=
  {p | p.val i = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.face ``Submission.DifferentialGeometry.Simplex.face


theorem isClosed_face {n : ℕ} (i : Fin (n + 2)) : IsClosed (face i) :=
  isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.isClosed_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.isClosed_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.isClosed_face ``Submission.DifferentialGeometry.Simplex.isClosed_face


theorem map_succAbove_apply_pivot {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex.map i.succAbove p).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove p i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.map_succAbove_apply_pivot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.map_succAbove_apply_pivot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.map_succAbove_apply_pivot ``Submission.DifferentialGeometry.Simplex.map_succAbove_apply_pivot


theorem map_succAbove_apply_image {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    (stdSimplex.map i.succAbove p).val (i.succAbove j) = p.val j := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove p (i.succAbove j) = p.val j
  rw [FunOnFinite.linearMap_apply_apply]
  simp only [Fin.succAbove_right_inj, Finset.filter_eq', Finset.mem_univ,
    if_true, Finset.sum_singleton]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.map_succAbove_apply_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.map_succAbove_apply_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.map_succAbove_apply_image ``Submission.DifferentialGeometry.Simplex.map_succAbove_apply_image


def faceInsert {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), face i) :=
  ⟨fun p ↦ ⟨stdSimplex.map i.succAbove p, map_succAbove_apply_pivot i p⟩,
    (stdSimplex.continuous_map i.succAbove).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceInsert ``Submission.DifferentialGeometry.Simplex.faceInsert


def faceDelete {n : ℕ} (i : Fin (n + 2)) :
    C(face i, stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun p ↦ ⟨fun j ↦ p.val.val (i.succAbove j),
    ⟨fun j ↦ p.val.property.1 _, by
      have hp := p.val.property.2
      rw [Fin.sum_univ_succAbove _ i, p.property, zero_add] at hp
      exact hp⟩⟩, by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply (i.succAbove j)).comp
      (continuous_subtype_val.comp continuous_subtype_val)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceDelete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceDelete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceDelete ``Submission.DifferentialGeometry.Simplex.faceDelete


@[simp]
theorem faceDelete_faceInsert {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) : faceDelete i (faceInsert i p) = p := by
  apply Subtype.ext
  funext j
  exact map_succAbove_apply_image i p j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceDelete_faceInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceDelete_faceInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceDelete_faceInsert ``Submission.DifferentialGeometry.Simplex.faceDelete_faceInsert


@[simp]
theorem faceInsert_faceDelete {n : ℕ} (i : Fin (n + 2)) (p : face i) :
    faceInsert i (faceDelete i p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    exact (map_succAbove_apply_pivot i _).trans p.property.symm
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
    exact map_succAbove_apply_image i _ j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceInsert_faceDelete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceInsert_faceDelete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceInsert_faceDelete ``Submission.DifferentialGeometry.Simplex.faceInsert_faceDelete


def faceHomeomorph {n : ℕ} (i : Fin (n + 2)) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ face i where
  toFun := faceInsert i
  invFun := faceDelete i
  left_inv := faceDelete_faceInsert i
  right_inv := faceInsert_faceDelete i
  continuous_toFun := (faceInsert i).continuous
  continuous_invFun := (faceDelete i).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceHomeomorph ``Submission.DifferentialGeometry.Simplex.faceHomeomorph

end DifferentialGeometry.Simplex
