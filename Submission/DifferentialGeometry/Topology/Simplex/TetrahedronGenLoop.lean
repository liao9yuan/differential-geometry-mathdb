import Submission.DifferentialGeometry.Topology.Simplex.TriangleGenLoop
import Submission.DifferentialGeometry.Topology.Simplex.CubeParametrization
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronConeHomotopy
import Submission.DifferentialGeometry.Topology.Homotopy.CoordinateSwap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.ContinuousMap
open scoped _root_.unitInterval
namespace DifferentialGeometry.Simplex
variable {X : Type*} [TopologicalSpace X]

def tetrahedronGenLoop (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) : GenLoop (Fin 3) X x :=
  ⟨⟨fun v => g (Simplex.tetrahedronJoin (v 2, v 1, v 0)), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    apply hg
    fin_cases i
    · rcases hi with h | h
      · exact ⟨3, by simp [tetrahedronJoin, show v 0 = 0 from h]⟩
      · exact ⟨2, by simp [tetrahedronJoin, show v 0 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨1, by simp [tetrahedronJoin, show v 1 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 1 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨2, by simp [tetrahedronJoin, show v 2 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 2 = 1 from h]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoop ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoop

@[simp] theorem tetrahedronGenLoop_apply (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) (v : Fin 3 → unitInterval) :
    tetrahedronGenLoop g x hg v = g (Simplex.tetrahedronJoin (v 2, v 1, v 0)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoop_apply ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoop_apply


def tetrahedronConeGenLoop (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) : GenLoop (Fin 3) X x :=
  ⟨⟨fun v => g (tetrahedronCone (v 2, v 1, v 0)), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    apply hg
    fin_cases i
    · rcases hi with h | h
      · exact ⟨3, by simp [tetrahedronCone, show v 0 = 0 from h]⟩
      · exact ⟨2, by simp [tetrahedronCone, show v 0 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨2, by simp [tetrahedronCone, show v 1 = 0 from h]⟩
      · exact ⟨1, by simp [tetrahedronCone, show v 1 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨1, by simp [tetrahedronCone, show v 2 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronCone, show v 2 = 1 from h]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronConeGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronConeGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronConeGenLoop ``Submission.DifferentialGeometry.Simplex.tetrahedronConeGenLoop

def tetrahedronConeGenLoopHomotopyRel (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (tetrahedronConeGenLoop g x hg).val.HomotopyRel
      (GenLoop.congr x (Equiv.swap (1 : Fin 3) 2) (tetrahedronGenLoop g x hg)).val
      (Cube.boundary (Fin 3)) where
  toContinuousMap := (tetrahedronConeHomotopyRel g hg).toContinuousMap.comp
    ⟨fun z => (z.1,z.2 2,z.2 1,z.2 0), by fun_prop⟩
  map_zero_left v := by
    change tetrahedronConeHomotopyRel g hg (0,v 2,v 1,v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left v := by
    change tetrahedronConeHomotopyRel g hg (1,v 2,v 1,v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    change g (tetrahedronJoin (v 1,v 2,v 0)) =
      g (tetrahedronJoin (v (Equiv.swap (1 : Fin 3) 2 2),
        v (Equiv.swap (1 : Fin 3) 2 1), v (Equiv.swap (1 : Fin 3) 2 0)))
    simp [Equiv.swap_apply_def]
  prop' t v hv := by
    have hb : (v 2,v 1,v 0) ∈ {p : unitInterval × unitInterval × unitInterval |
        p.1 = 0 ∨ p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 0 ∨ p.2.2 = 1} := by
      obtain ⟨i,hi⟩ := hv
      fin_cases i
      · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
      · rcases hi with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases hi with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    exact (tetrahedronConeHomotopyRel g hg).eq_fst t hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronConeGenLoopHomotopyRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronConeGenLoopHomotopyRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronConeGenLoopHomotopyRel ``Submission.DifferentialGeometry.Simplex.tetrahedronConeGenLoopHomotopyRel

theorem tetrahedronConeGenLoop_class_eq_inv (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (⟦tetrahedronConeGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
      ((·⁻¹) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x)
        ⟦tetrahedronGenLoop g x hg⟧ := by
  have h : (⟦tetrahedronConeGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
      (⟦GenLoop.congr x (Equiv.swap (1 : Fin 3) 2) (tetrahedronGenLoop g x hg)⟧ :
        HomotopyGroup (Fin 3) X x) :=
    Quotient.sound ⟨tetrahedronConeGenLoopHomotopyRel g x hg⟩
  exact h.trans
    (Topology.homotopyGroup_swap_eq_inv_of_ne 1 2 (by decide) (tetrahedronGenLoop g x hg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronConeGenLoop_class_eq_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronConeGenLoop_class_eq_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronConeGenLoop_class_eq_inv ``Submission.DifferentialGeometry.Simplex.tetrahedronConeGenLoop_class_eq_inv

end DifferentialGeometry.Simplex
