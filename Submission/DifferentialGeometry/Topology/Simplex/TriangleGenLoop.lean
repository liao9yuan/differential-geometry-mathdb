import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Submission.DifferentialGeometry.Topology.Homotopy.CubeCompactification
import Submission.DifferentialGeometry.Topology.Simplex.CubeParametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.ContinuousMap
open scoped _root_.unitInterval

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def triangleGenLoop (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => g (triangleJoin (v 0, v 1)),
    g.continuous.comp (triangleJoin.continuous.comp
      ((continuous_apply 0).prodMk (continuous_apply 1)))⟩, by
    rintro v ⟨i, hi⟩
    change g (triangleJoin (v 0, v 1)) = x
    fin_cases i
    · rcases hi with hi | hi
      · rw [show v 0 = 0 from hi, triangleJoin_zero]
        exact hg _ ⟨1, by simp⟩
      · rw [show v 0 = 1 from hi, triangleJoin_one]
        exact hg _ ⟨0, map_succAbove_apply_pivot _ _⟩
    · rcases hi with hi | hi
      · rw [show v 1 = 0 from hi, triangleJoin_second_zero]
        exact hg _ ⟨2, map_succAbove_apply_pivot _ _⟩
      · rw [show v 1 = 1 from hi, triangleJoin_second_one]
        exact hg _ ⟨1, map_succAbove_apply_pivot _ _⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleGenLoop ``Submission.DifferentialGeometry.Simplex.triangleGenLoop

@[simp] theorem triangleGenLoop_apply (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) (v : Fin 2 → unitInterval) :
    triangleGenLoop g x hg v = g (triangleJoin (v 0, v 1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleGenLoop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleGenLoop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleGenLoop_apply ``Submission.DifferentialGeometry.Simplex.triangleGenLoop_apply

end DifferentialGeometry.Simplex
