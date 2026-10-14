import Submission.DifferentialGeometry.Topology.Simplex.Face
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace stdSimplex
open _root_.stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] {n : ℕ}

open _root_.stdSimplex in
theorem map_succAbove_map_succAbove (i : Fin (n + 2)) (j : Fin (n + 1))
    (p : stdSimplex S (Fin n)) :
    _root_.stdSimplex.map i.succAbove (_root_.stdSimplex.map j.succAbove p) =
      map (i.succAbove j).succAbove (_root_.stdSimplex.map (j.predAbove i).succAbove p) := by
  rw [_root_.stdSimplex.map_comp_apply, _root_.stdSimplex.map_comp_apply]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.map_succAbove_map_succAbove then
    throwError "Refusing to shadow existing declaration stdSimplex.map_succAbove_map_succAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.map_succAbove_map_succAbove ``Submission.stdSimplex.map_succAbove_map_succAbove

end stdSimplex

namespace DifferentialGeometry.Simplex

variable {n : ℕ}

theorem faceInsert_faceInsert_val (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (faceInsert i (faceInsert j p).val).val =
      (faceInsert (i.succAbove j) (faceInsert (j.predAbove i) p).val).val :=
  stdSimplex.map_succAbove_map_succAbove i j p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceInsert_faceInsert_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceInsert_faceInsert_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceInsert_faceInsert_val ``Submission.DifferentialGeometry.Simplex.faceInsert_faceInsert_val

theorem boundary_face_point_eq (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (⟨stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p),
      ⟨i, map_succAbove_apply_pivot i _⟩⟩ : boundary (Fin (n + 3))) =
    ⟨stdSimplex.map (i.succAbove j).succAbove
      (stdSimplex.map (j.predAbove i).succAbove p),
      ⟨i.succAbove j, map_succAbove_apply_pivot (i.succAbove j) _⟩⟩ :=
  Subtype.ext (stdSimplex.map_succAbove_map_succAbove i j p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundary_face_point_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundary_face_point_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundary_face_point_eq ``Submission.DifferentialGeometry.Simplex.boundary_face_point_eq

theorem face_restriction_compatibility {X : Type*}
    (f : Fin (n + 3) → stdSimplex ℝ (Fin (n + 2)) → X)
    (g : boundary (Fin (n + 3)) → X)
    (hf : ∀ (i : Fin (n + 3)) (q : stdSimplex ℝ (Fin (n + 2))),
      f i q = g ⟨stdSimplex.map i.succAbove q, ⟨i, map_succAbove_apply_pivot i q⟩⟩)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (p : stdSimplex ℝ (Fin (n + 1))) :
    f i (stdSimplex.map j.succAbove p) =
      f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
  rw [hf, hf, boundary_face_point_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.face_restriction_compatibility then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.face_restriction_compatibility"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.face_restriction_compatibility ``Submission.DifferentialGeometry.Simplex.face_restriction_compatibility

end DifferentialGeometry.Simplex
