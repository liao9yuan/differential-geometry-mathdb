import Submission.DifferentialGeometry.Topology.Homotopy.Reindex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.ContinuousMap
open scoped _root_.unitInterval

namespace DifferentialGeometry.Topology

private def squareSwapDenom (r : unitInterval) : ℝ :=
  (1 - (r : ℝ)) ^ 2 + (r : ℝ) ^ 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapDenom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapDenom target :: scope.openDecls } }

private theorem squareSwapDenom_pos (r : unitInterval) : 0 < squareSwapDenom r := by
  dsimp [squareSwapDenom]
  nlinarith [sq_nonneg ((r : ℝ) - 1 / 2)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapDenom_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapDenom_pos target :: scope.openDecls } }

private def squareSwapRaw (r : unitInterval) (v : Fin 2 → unitInterval) : Fin 2 → ℝ :=
  ![((1 - (r : ℝ)) * (2 * (v 1 : ℝ) - 1) - (r : ℝ) * (2 * (v 0 : ℝ) - 1)) /
      squareSwapDenom r,
    ((1 - (r : ℝ)) * (2 * (v 0 : ℝ) - 1) + (r : ℝ) * (2 * (v 1 : ℝ) - 1)) /
      squareSwapDenom r]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapRaw
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapRaw target :: scope.openDecls } }

private theorem squareSwapRaw_inverse_zero (r : unitInterval) (v : Fin 2 → unitInterval) :
    (1 - (r : ℝ)) * squareSwapRaw r v 1 - (r : ℝ) * squareSwapRaw r v 0 =
      2 * (v 0 : ℝ) - 1 := by
  simp only [squareSwapRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [ne_of_gt (squareSwapDenom_pos r)]
  dsimp [squareSwapDenom]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapRaw_inverse_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapRaw_inverse_zero target :: scope.openDecls } }

private theorem squareSwapRaw_inverse_one (r : unitInterval) (v : Fin 2 → unitInterval) :
    (1 - (r : ℝ)) * squareSwapRaw r v 0 + (r : ℝ) * squareSwapRaw r v 1 =
      2 * (v 1 : ℝ) - 1 := by
  simp only [squareSwapRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [ne_of_gt (squareSwapDenom_pos r)]
  dsimp [squareSwapDenom]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapRaw_inverse_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapRaw_inverse_one target :: scope.openDecls } }

private def squareSwapParam :
    C(unitInterval × (Fin 2 → unitInterval), Fin 2 → unitInterval) where
  toFun p i := _root_.Set.projIcc 0 1 zero_le_one ((squareSwapRaw p.1 p.2 i + 1) / 2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_projIcc.comp
    apply Continuous.div_const
    apply Continuous.add_const
    have hd : Continuous (fun p : unitInterval × (Fin 2 → unitInterval) => squareSwapDenom p.1) := by
      dsimp [squareSwapDenom]
      fun_prop
    fin_cases i <;> dsimp [squareSwapRaw] <;>
      exact Continuous.div (by fun_prop) hd (fun p => ne_of_gt (squareSwapDenom_pos p.1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapParam target :: scope.openDecls } }

private theorem convex_combo_strict (r : unitInterval) (a b : ℝ)
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1) :
    -1 < (1 - (r : ℝ)) * a + (r : ℝ) * b ∧
      (1 - (r : ℝ)) * a + (r : ℝ) * b < 1 := by
  exact convex_Ioo (-1 : ℝ) 1 ha hb (sub_nonneg.mpr r.property.2) r.property.1 (by ring)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.convex_combo_strict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.convex_combo_strict target :: scope.openDecls } }

private theorem squareSwapParam_boundary (r : unitInterval) (v : Fin 2 → unitInterval)
    (hv : v ∈ Cube.boundary (Fin 2)) : squareSwapParam (r, v) ∈ Cube.boundary (Fin 2) := by
  by_contra h
  have hi (i : Fin 2) : -1 < squareSwapRaw r v i ∧ squareSwapRaw r v i < 1 := by
    have h0 : ¬ squareSwapParam (r, v) i = 0 := fun hi => h ⟨i, Or.inl hi⟩
    have h1 : ¬ squareSwapParam (r, v) i = 1 := fun hi => h ⟨i, Or.inr hi⟩
    have hlo : 0 < (squareSwapRaw r v i + 1) / 2 := by
      by_contra hh
      apply h0
      exact _root_.Set.projIcc_of_le_left zero_le_one (le_of_not_gt hh)
    have hhi : (squareSwapRaw r v i + 1) / 2 < 1 := by
      by_contra hh
      apply h1
      exact _root_.Set.projIcc_of_right_le zero_le_one (le_of_not_gt hh)
    constructor <;> linarith
  have hzero := convex_combo_strict r (squareSwapRaw r v 1) (-squareSwapRaw r v 0)
    (hi 1) (by constructor <;> linarith [(hi 0).1, (hi 0).2])
  have hone := convex_combo_strict r (squareSwapRaw r v 0) (squareSwapRaw r v 1) (hi 0) (hi 1)
  rw [mul_neg, ← sub_eq_add_neg, squareSwapRaw_inverse_zero] at hzero
  rw [squareSwapRaw_inverse_one] at hone
  rcases hv with ⟨i, hi⟩
  fin_cases i <;> rcases hi with hi | hi
  · change v 0 = 0 at hi
    rw [hi] at hzero
    norm_num at hzero
  · change v 0 = 1 at hi
    rw [hi] at hzero
    norm_num at hzero
  · change v 1 = 0 at hi
    rw [hi] at hone
    norm_num at hone
  · change v 1 = 1 at hi
    rw [hi] at hone
    norm_num at hone

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapParam_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapParam_boundary target :: scope.openDecls } }

private theorem squareSwapParam_zero (v : Fin 2 → unitInterval) :
    squareSwapParam (0, v) = fun i => v ((Equiv.swap (0 : Fin 2) 1) i) := by
  funext i
  fin_cases i
  · change _root_.Set.projIcc 0 1 zero_le_one _ = v 1
    convert _root_.Set.projIcc_of_mem zero_le_one (v 1).property using 1
    simp [squareSwapRaw, squareSwapDenom]
  · change _root_.Set.projIcc 0 1 zero_le_one _ = v 0
    convert _root_.Set.projIcc_of_mem zero_le_one (v 0).property using 1
    simp [squareSwapRaw, squareSwapDenom]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapParam_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapParam_zero target :: scope.openDecls } }

private theorem squareSwapParam_one (v : Fin 2 → unitInterval) :
    squareSwapParam (1, v) = fun i => if i = 0 then unitInterval.symm (v 0) else v i := by
  funext i
  fin_cases i
  · change _root_.Set.projIcc 0 1 zero_le_one ((squareSwapRaw 1 v 0 + 1) / 2) = unitInterval.symm (v 0)
    have he : (squareSwapRaw 1 v 0 + 1) / 2 = (unitInterval.symm (v 0) : ℝ) := by
      norm_num [squareSwapRaw, squareSwapDenom, unitInterval.symm]
      ring
    rw [he]
    exact _root_.Set.projIcc_of_mem zero_le_one (unitInterval.symm (v 0)).property
  · change _root_.Set.projIcc 0 1 zero_le_one _ = v 1
    convert _root_.Set.projIcc_of_mem zero_le_one (v 1).property using 1
    simp [squareSwapRaw, squareSwapDenom]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.squareSwapParam_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.squareSwapParam_one target :: scope.openDecls } }


private def cubeSwapParam {N : Type*} [DecidableEq N] (i j : N) :
    C(unitInterval × (N → unitInterval), N → unitInterval) where
  toFun p k := if k = i then squareSwapParam (p.1, ![p.2 i, p.2 j]) 0
    else if k = j then squareSwapParam (p.1, ![p.2 i, p.2 j]) 1 else p.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    split_ifs <;> fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cubeSwapParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cubeSwapParam target :: scope.openDecls } }

private theorem cubeSwapParam_boundary {N : Type*} [DecidableEq N] (i j : N) (hij : i ≠ j)
    (r : unitInterval) (v : N → unitInterval) (hv : v ∈ Cube.boundary N) :
    cubeSwapParam i j (r,v) ∈ Cube.boundary N := by
  obtain ⟨k,hk⟩ := hv
  by_cases hki : k = i
  · subst k
    have hb : (![v i,v j] : Fin 2 → unitInterval) ∈ Cube.boundary (Fin 2) := ⟨0, by simpa using hk⟩
    obtain ⟨a,ha⟩ := squareSwapParam_boundary r ![v i,v j] hb
    fin_cases a
    · exact ⟨i, by simpa [cubeSwapParam] using ha⟩
    · exact ⟨j, by simpa [cubeSwapParam, hij.symm] using ha⟩
  · by_cases hkj : k = j
    · subst k
      have hb : (![v i,v j] : Fin 2 → unitInterval) ∈ Cube.boundary (Fin 2) := ⟨1, by simpa using hk⟩
      obtain ⟨a,ha⟩ := squareSwapParam_boundary r ![v i,v j] hb
      fin_cases a
      · exact ⟨i, by simpa [cubeSwapParam] using ha⟩
      · exact ⟨j, by simpa [cubeSwapParam, hij.symm] using ha⟩
    · exact ⟨k, by simpa [cubeSwapParam, hki, hkj] using hk⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cubeSwapParam_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cubeSwapParam_boundary target :: scope.openDecls } }

private theorem cubeSwapParam_zero {N : Type*} [DecidableEq N] (i j : N) (hij : i ≠ j)
    (v : N → unitInterval) : cubeSwapParam i j (0,v) = fun k => v ((Equiv.swap i j) k) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [cubeSwapParam, squareSwapParam_zero]
  · by_cases hkj : k = j
    · subst k
      simp [cubeSwapParam, squareSwapParam_zero, hij.symm]
    · simp [cubeSwapParam, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cubeSwapParam_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cubeSwapParam_zero target :: scope.openDecls } }

private theorem cubeSwapParam_one {N : Type*} [DecidableEq N] (i j : N) (hij : i ≠ j)
    (v : N → unitInterval) :
    cubeSwapParam i j (1,v) = fun k => if k = i then unitInterval.symm (v i) else v k := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [cubeSwapParam, squareSwapParam_one]
  · by_cases hkj : k = j
    · subst k
      simp [cubeSwapParam, squareSwapParam_one, hij.symm]
    · simp [cubeSwapParam, hki, hkj]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cubeSwapParam_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cubeSwapParam_one target :: scope.openDecls } }

def genLoopSwapHomotopyRelOfNe {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x : X}
    (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    (GenLoop.congr x (Equiv.swap i j) p).val.HomotopyRel
      (GenLoop.symmAt i p).val (Cube.boundary N) where
  toContinuousMap := p.val.comp (cubeSwapParam i j)
  map_zero_left v := by
    change p (cubeSwapParam i j (0,v)) = _
    rw [cubeSwapParam_zero i j hij]
    rfl
  map_one_left v := by
    change p (cubeSwapParam i j (1,v)) = _
    rw [cubeSwapParam_one i j hij]
    rfl
  prop' r v hv := by
    change p (cubeSwapParam i j (r,v)) = _
    rw [GenLoop.boundary p _ (cubeSwapParam_boundary i j hij r v hv)]
    exact (GenLoop.boundary (GenLoop.congr x (Equiv.swap i j) p) v hv).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSwapHomotopyRelOfNe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSwapHomotopyRelOfNe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSwapHomotopyRelOfNe ``Submission.DifferentialGeometry.Topology.genLoopSwapHomotopyRelOfNe

theorem homotopyGroup_swap_eq_inv_of_ne {N X : Type*} [DecidableEq N] [TopologicalSpace X]
    {x : X} (i j : N) (hij : i ≠ j) (p : GenLoop N X x) [Nonempty N] :
    (⟦GenLoop.congr x (Equiv.swap i j) p⟧ : HomotopyGroup N X x) =
      ((⟦p⟧)⁻¹ : HomotopyGroup N X x) := by
  rw [HomotopyGroup.inv_spec (i := i)]
  exact Quotient.sound ⟨genLoopSwapHomotopyRelOfNe i j hij p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv_of_ne ``Submission.DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv_of_ne

def genLoopSwapHomotopyRel {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) p).val.HomotopyRel
      (GenLoop.symmAt 0 p).val (Cube.boundary (Fin 2)) :=
  genLoopSwapHomotopyRelOfNe 0 1 (by decide) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSwapHomotopyRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSwapHomotopyRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSwapHomotopyRel ``Submission.DifferentialGeometry.Topology.genLoopSwapHomotopyRel

theorem homotopyGroup_swap_eq_inv {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (⟦GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) p⟧ : HomotopyGroup (Fin 2) X x) =
      ((⟦p⟧)⁻¹ : HomotopyGroup (Fin 2) X x) :=
  homotopyGroup_swap_eq_inv_of_ne 0 1 (by decide) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv ``Submission.DifferentialGeometry.Topology.homotopyGroup_swap_eq_inv

end DifferentialGeometry.Topology
