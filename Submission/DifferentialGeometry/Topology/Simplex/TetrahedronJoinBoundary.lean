import Submission.DifferentialGeometry.Topology.Simplex.CubeParametrization
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.Homotopy.HomotopyGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Simplex

open scoped _root_.unitInterval

theorem tetrahedronJoin_mem_boundary_iff (v : Fin 3 → unitInterval) :
    tetrahedronJoin (v 2, v 1, v 0) ∈ boundary (Fin 4) ↔ v ∈ Cube.boundary (Fin 3) := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · change (1 - (v 2 : ℝ)) * (1 - (v 1 : ℝ)) = 0 at hi
      rcases mul_eq_zero.mp hi with h | h
      · exact ⟨2, Or.inr (Subtype.ext (by dsimp; linarith))⟩
      · exact ⟨1, Or.inr (Subtype.ext (by dsimp; linarith))⟩
    · change (1 - (v 2 : ℝ)) * (v 1 : ℝ) = 0 at hi
      rcases mul_eq_zero.mp hi with h | h
      · exact ⟨2, Or.inr (Subtype.ext (by dsimp; linarith))⟩
      · exact ⟨1, Or.inl (Subtype.ext h)⟩
    · change (v 2 : ℝ) * (1 - (v 0 : ℝ)) = 0 at hi
      rcases mul_eq_zero.mp hi with h | h
      · exact ⟨2, Or.inl (Subtype.ext h)⟩
      · exact ⟨0, Or.inr (Subtype.ext (by dsimp; linarith))⟩
    · change (v 2 : ℝ) * (v 0 : ℝ) = 0 at hi
      rcases mul_eq_zero.mp hi with h | h
      · exact ⟨2, Or.inl (Subtype.ext h)⟩
      · exact ⟨0, Or.inl (Subtype.ext h)⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · rcases hi with h | h
      · exact ⟨3, by simp [tetrahedronJoin, show v 0 = 0 from h]⟩
      · exact ⟨2, by simp [tetrahedronJoin, show v 0 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨1, by simp [tetrahedronJoin, show v 1 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 1 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨2, by simp [tetrahedronJoin, show v 2 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 2 = 1 from h]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_mem_boundary_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_mem_boundary_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_mem_boundary_iff ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_mem_boundary_iff

end DifferentialGeometry.Simplex
