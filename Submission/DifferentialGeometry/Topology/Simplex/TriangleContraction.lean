import Submission.DifferentialGeometry.Topology.Simplex.CubeParametrization
import Submission.DifferentialGeometry.Topology.Simplex.VertexContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

theorem vertexContraction_zero_face_zero (t : unitInterval)
    (p : stdSimplex ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, stdSimplex.map (0 : Fin 3).succAbove p) =
      triangleJoin (unitInterval.symm t, stdSimplexHomeomorphUnitInterval p) := by
  apply Subtype.ext
  funext i
  rw [vertexContraction_apply]
  fin_cases i
  · have h := map_succAbove_apply_pivot (0 : Fin 3) p
    change (1 - (t : ℝ)) * (stdSimplex.map (0 : Fin 3).succAbove p).val 0 +
      (t : ℝ) * 1 = 1 - (1 - (t : ℝ))
    rw [h]
    ring
  · have h := map_succAbove_apply_image (0 : Fin 3) p (0 : Fin 2)
    change (stdSimplex.map (0 : Fin 3).succAbove p).val 1 = p.val 0 at h
    change (1 - (t : ℝ)) * (stdSimplex.map (0 : Fin 3).succAbove p).val 1 +
      (t : ℝ) * 0 = (1 - (t : ℝ)) * (1 - p.val 1)
    rw [h]
    have hp := stdSimplex.add_eq_one p
    change p.val 0 + p.val 1 = 1 at hp
    have hp0 : p.val 0 = 1 - p.val 1 := by linarith
    rw [hp0]
    ring
  · have h := map_succAbove_apply_image (0 : Fin 3) p (1 : Fin 2)
    change (stdSimplex.map (0 : Fin 3).succAbove p).val 2 = p.val 1 at h
    change (1 - (t : ℝ)) * (stdSimplex.map (0 : Fin 3).succAbove p).val 2 +
      (t : ℝ) * 0 = (1 - (t : ℝ)) * p.val 1
    rw [h]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero_face_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero_face_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero_face_zero ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero_face_zero

theorem vertexContraction_zero_face_one (t : unitInterval)
    (p : stdSimplex ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, stdSimplex.map (1 : Fin 3).succAbove p) =
      stdSimplex.map (1 : Fin 3).succAbove (vertexContraction (0 : Fin 2) (t, p)) := by
  simpa using vertexContraction_map (1 : Fin 3).succAbove (0 : Fin 2) t p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero_face_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero_face_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero_face_one ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero_face_one

theorem vertexContraction_zero_face_two (t : unitInterval)
    (p : stdSimplex ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, stdSimplex.map (2 : Fin 3).succAbove p) =
      stdSimplex.map (2 : Fin 3).succAbove (vertexContraction (0 : Fin 2) (t, p)) := by
  simpa using vertexContraction_map (2 : Fin 3).succAbove (0 : Fin 2) t p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero_face_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero_face_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero_face_two ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero_face_two

end DifferentialGeometry.Simplex
