import Submission.DifferentialGeometry.Topology.Simplex.Face

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.unitInterval

namespace DifferentialGeometry.Simplex

def triangleJoin : C(unitInterval × unitInterval, stdSimplex ℝ (Fin 3)) where
  toFun x := ⟨![1 - (x.1 : ℝ), (x.1 : ℝ) * (1 - (x.2 : ℝ)), (x.1 : ℝ) * (x.2 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.2.1
      have hb1 := x.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoin ``Submission.DifferentialGeometry.Simplex.triangleJoin

@[simp] theorem triangleJoin_zero (v : unitInterval) :
    triangleJoin (0, v) = stdSimplex.vertex (0 : Fin 3) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [triangleJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoin_zero ``Submission.DifferentialGeometry.Simplex.triangleJoin_zero

@[simp] theorem triangleJoin_one (v : unitInterval) :
    triangleJoin (1, v) = stdSimplex.map (0 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm v) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoin_one ``Submission.DifferentialGeometry.Simplex.triangleJoin_one

@[simp] theorem triangleJoin_second_zero (s : unitInterval) :
    triangleJoin (s, 0) = stdSimplex.map (2 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm s) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 2
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoin_second_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoin_second_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoin_second_zero ``Submission.DifferentialGeometry.Simplex.triangleJoin_second_zero

@[simp] theorem triangleJoin_second_one (s : unitInterval) :
    triangleJoin (s, 1) = stdSimplex.map (1 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm s) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 1
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoin_second_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoin_second_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoin_second_one ``Submission.DifferentialGeometry.Simplex.triangleJoin_second_one

def triangleJoinReverse : C(unitInterval × unitInterval, stdSimplex ℝ (Fin 3)) where
  toFun x := ⟨![(1 - (x.1 : ℝ)) * (1 - (x.2 : ℝ)),
      (1 - (x.1 : ℝ)) * (x.2 : ℝ), (x.1 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.2.1
      have hb1 := x.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleJoinReverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleJoinReverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleJoinReverse ``Submission.DifferentialGeometry.Simplex.triangleJoinReverse

def tetrahedronJoin : C(unitInterval × unitInterval × unitInterval, stdSimplex ℝ (Fin 4)) where
  toFun x := ⟨![(1 - (x.1 : ℝ)) * (1 - (x.2.1 : ℝ)),
      (1 - (x.1 : ℝ)) * (x.2.1 : ℝ), (x.1 : ℝ) * (1 - (x.2.2 : ℝ)),
      (x.1 : ℝ) * (x.2.2 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.1.2.1
      have hb1 := x.2.1.2.2
      have hc0 := x.2.2.2.1
      have hc1 := x.2.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin

@[simp] theorem tetrahedronJoin_zero (t u : unitInterval) :
    (tetrahedronJoin (0, t, u)).val = ![1 - (t : ℝ), (t : ℝ), 0, 0] := by
  funext i
  fin_cases i <;> simp [tetrahedronJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_zero ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_zero

@[simp] theorem tetrahedronJoin_one (t u : unitInterval) :
    (tetrahedronJoin (1, t, u)).val = ![0, 0, 1 - (u : ℝ), (u : ℝ)] := by
  funext i
  fin_cases i <;> simp [tetrahedronJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_one ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_one

@[simp] theorem tetrahedronJoin_middle_zero (s u : unitInterval) :
    tetrahedronJoin (s, 0, u) = stdSimplex.map (1 : Fin 4).succAbove (triangleJoin (s, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 1
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoin, Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_middle_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_middle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_middle_zero ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_middle_zero

@[simp] theorem tetrahedronJoin_middle_one (s u : unitInterval) :
    tetrahedronJoin (s, 1, u) = stdSimplex.map (0 : Fin 4).succAbove (triangleJoin (s, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoin, Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_middle_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_middle_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_middle_one ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_middle_one

@[simp] theorem tetrahedronJoin_last_zero (s t : unitInterval) :
    tetrahedronJoin (s, t, 0) = stdSimplex.map (3 : Fin 4).succAbove
      (triangleJoinReverse (s, t)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 3
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoinReverse, Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_last_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_last_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_last_zero ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_last_zero

@[simp] theorem tetrahedronJoin_last_one (s t : unitInterval) :
    tetrahedronJoin (s, t, 1) = stdSimplex.map (2 : Fin 4).succAbove
      (triangleJoinReverse (s, t)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 2
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoinReverse, Fin.succAbove]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronJoin_last_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronJoin_last_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronJoin_last_one ``Submission.DifferentialGeometry.Simplex.tetrahedronJoin_last_one

end DifferentialGeometry.Simplex
