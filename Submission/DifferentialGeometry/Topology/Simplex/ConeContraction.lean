import Submission.DifferentialGeometry.Topology.Simplex.Cone
import Submission.DifferentialGeometry.Topology.Simplex.VertexContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

theorem vertexContraction_zero_face_eq_simplexCone (n : ℕ) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    vertexContraction (0 : Fin (n + 2)) (t, stdSimplex.map (0 : Fin (n + 2)).succAbove p) =
      simplexCone n (t, p) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [vertexContraction_apply, simplexCone_apply_zero, map_succAbove_apply_pivot]
    simp
  · rw [vertexContraction_apply, simplexCone_apply_succ]
    have h := map_succAbove_apply_image (0 : Fin (n + 2)) p j
    simp only [Fin.succAbove_zero] at h ⊢
    rw [h]
    simp [eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero_face_eq_simplexCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero_face_eq_simplexCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero_face_eq_simplexCone ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero_face_eq_simplexCone

theorem vertexContraction_zero_face_succ (n : ℕ) (i : Fin (n + 1)) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    vertexContraction (0 : Fin (n + 2)) (t, stdSimplex.map i.succ.succAbove p) =
      stdSimplex.map i.succ.succAbove (vertexContraction (0 : Fin (n + 1)) (t, p)) := by
  simpa only [Fin.succ_succAbove_zero] using
    vertexContraction_map i.succ.succAbove (0 : Fin (n + 1)) t p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero_face_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero_face_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero_face_succ ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero_face_succ

end DifferentialGeometry.Simplex
