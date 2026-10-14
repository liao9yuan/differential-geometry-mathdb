import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.UhlenbeckReaction
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Dim3Reaction

open scoped _root_.BigOperators

def ricciFromSectional3 (K12 K13 K23 : Real) (i j : Fin 3) : Real :=
  if i = j then
    if i = 0 then K12 + K13 else if i = 1 then K12 + K23 else K13 + K23
  else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.ricciFromSectional3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.ricciFromSectional3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.ricciFromSectional3 ``Submission.DifferentialGeometry.Dim3Reaction.ricciFromSectional3

theorem ricciFromSectional3_symm (K12 K13 K23 : Real) (i j : Fin 3) :
    ricciFromSectional3 K12 K13 K23 i j =
      ricciFromSectional3 K12 K13 K23 j i := by
  fin_cases i <;> fin_cases j <;> simp [ricciFromSectional3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.ricciFromSectional3_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.ricciFromSectional3_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.ricciFromSectional3_symm ``Submission.DifferentialGeometry.Dim3Reaction.ricciFromSectional3_symm

def bivectorCoordinate3 (a b : Fin 3) (v w : Fin 3 → Real) : Real :=
  v a * w b - v b * w a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.bivectorCoordinate3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.bivectorCoordinate3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.bivectorCoordinate3 ``Submission.DifferentialGeometry.Dim3Reaction.bivectorCoordinate3

def curvatureTensorEval3
    (A : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (v w z u : Fin 3 → Real) : Real :=
  ∑ a, ∑ b, ∑ c, ∑ d, v a * w b * z c * u d * A a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureTensorEval3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureTensorEval3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureTensorEval3 ``Submission.DifferentialGeometry.Dim3Reaction.curvatureTensorEval3

def curvatureOperatorQuadraticEval3 {n : Nat}
    (A : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) : Real :=
  ∑ i, ∑ j, c i * c j * curvatureTensorEval3 A (v i) (w i) (w j) (v j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3 ``Submission.DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3

theorem curvatureTensorEval3_rm (K12 K13 K23 : Real)
    (v w z u : Fin 3 → Real) :
    curvatureTensorEval3 (rm (ricciFromSectional3 K12 K13 K23)) v w z u =
      K12 * bivectorCoordinate3 0 1 v w * bivectorCoordinate3 0 1 u z +
      K13 * bivectorCoordinate3 0 2 v w * bivectorCoordinate3 0 2 u z +
      K23 * bivectorCoordinate3 1 2 v w * bivectorCoordinate3 1 2 u z := by
  unfold curvatureTensorEval3 rm ricciFromSectional3 sc kd bivectorCoordinate3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureTensorEval3_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureTensorEval3_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureTensorEval3_rm ``Submission.DifferentialGeometry.Dim3Reaction.curvatureTensorEval3_rm

private theorem weighted_sum_square {n : Nat}
    (c a : Fin n → Real) (K : Real) :
    (∑ i, ∑ j, c i * c j * (K * a i * a j)) =
      K * (∑ i, c i * a i) ^ 2 := by
  rw [sq, Fintype.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Dim3Reaction.weighted_sum_square
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Dim3Reaction.weighted_sum_square target :: scope.openDecls } }

theorem curvatureOperatorQuadraticEval3_rm {n : Nat}
    (K12 K13 K23 : Real) (c : Fin n → Real)
    (v w : Fin n → Fin 3 → Real) :
    curvatureOperatorQuadraticEval3
        (rm (ricciFromSectional3 K12 K13 K23)) c v w =
      K12 * (∑ i, c i * bivectorCoordinate3 0 1 (v i) (w i)) ^ 2 +
      K13 * (∑ i, c i * bivectorCoordinate3 0 2 (v i) (w i)) ^ 2 +
      K23 * (∑ i, c i * bivectorCoordinate3 1 2 (v i) (w i)) ^ 2 := by
  unfold curvatureOperatorQuadraticEval3
  simp_rw [curvatureTensorEval3_rm, mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j,
      c i * c j * (K12 * bivectorCoordinate3 0 1 (v i) (w i) *
        bivectorCoordinate3 0 1 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 0 1 (v i) (w i)) K12]
  rw [show (∑ i, ∑ j,
      c i * c j * (K13 * bivectorCoordinate3 0 2 (v i) (w i) *
        bivectorCoordinate3 0 2 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 0 2 (v i) (w i)) K13]
  rw [show (∑ i, ∑ j,
      c i * c j * (K23 * bivectorCoordinate3 1 2 (v i) (w i) *
        bivectorCoordinate3 1 2 (v j) (w j))) = _ by
    exact weighted_sum_square c (fun i ↦ bivectorCoordinate3 1 2 (v i) (w i)) K23]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm ``Submission.DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm

theorem curvatureOperatorQuadraticEval3_rm_nonneg {n : Nat}
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) :
    0 ≤ curvatureOperatorQuadraticEval3
      (rm (ricciFromSectional3 K12 K13 K23)) c v w := by
  rw [curvatureOperatorQuadraticEval3_rm]
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm_nonneg ``Submission.DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm_nonneg

def sectionalReaction12 (K12 K13 K23 : Real) : Real :=
  2 * (K12 ^ 2 + K13 * K23)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction12 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction12"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction12 ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction12

def sectionalReaction13 (K12 K13 K23 : Real) : Real :=
  2 * (K13 ^ 2 + K12 * K23)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction13 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction13"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction13 ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction13

def sectionalReaction23 (K12 K13 K23 : Real) : Real :=
  2 * (K23 ^ 2 + K12 * K13)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction23 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction23"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction23 ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction23

def curvatureTensorReaction3 (K12 K13 K23 : Real)
    (a b c d : Fin 3) : Real :=
  -2 * Bsharp (ricciFromSectional3 K12 K13 K23) a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3 ``Submission.DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3

theorem curvatureTensorReaction3_eq_rm (K12 K13 K23 : Real)
    (a b c d : Fin 3) :
    curvatureTensorReaction3 K12 K13 K23 a b c d =
      rm (ricciFromSectional3
        (sectionalReaction12 K12 K13 K23)
        (sectionalReaction13 K12 K13 K23)
        (sectionalReaction23 K12 K13 K23)) a b c d := by
  let R := ricciFromSectional3 K12 K13 K23
  have hsym : ∀ i j, R i j = R j i := by
    exact ricciFromSectional3_symm K12 K13 K23
  rw [curvatureTensorReaction3, bsharp_eq_knC hsym]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [knC, cc_closed hsym, R, rm, ricciFromSectional3,
      sectionalReaction12, sectionalReaction13, sectionalReaction23, sc, Rsq, normSq, kd,
      Fin.sum_univ_three] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3_eq_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3_eq_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3_eq_rm ``Submission.DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3_eq_rm

theorem sectionalReaction12_nonneg (K12 K13 K23 : Real)
    (h13 : 0 ≤ K13) (h23 : 0 ≤ K23) :
    0 ≤ sectionalReaction12 K12 K13 K23 := by
  unfold sectionalReaction12
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction12_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction12_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction12_nonneg ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction12_nonneg

theorem sectionalReaction13_nonneg (K12 K13 K23 : Real)
    (h12 : 0 ≤ K12) (h23 : 0 ≤ K23) :
    0 ≤ sectionalReaction13 K12 K13 K23 := by
  unfold sectionalReaction13
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction13_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction13_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction13_nonneg ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction13_nonneg

theorem sectionalReaction23_nonneg (K12 K13 K23 : Real)
    (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) :
    0 ≤ sectionalReaction23 K12 K13 K23 := by
  unfold sectionalReaction23
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.sectionalReaction23_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.sectionalReaction23_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.sectionalReaction23_nonneg ``Submission.DifferentialGeometry.Dim3Reaction.sectionalReaction23_nonneg

theorem curvatureOperatorQuadraticEval3_reaction {n : Nat}
    (K12 K13 K23 : Real) (c : Fin n → Real)
    (v w : Fin n → Fin 3 → Real) :
    curvatureOperatorQuadraticEval3 (curvatureTensorReaction3 K12 K13 K23) c v w =
      sectionalReaction12 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 0 1 (v i) (w i)) ^ 2 +
        sectionalReaction13 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 0 2 (v i) (w i)) ^ 2 +
        sectionalReaction23 K12 K13 K23 *
          (∑ i, c i * bivectorCoordinate3 1 2 (v i) (w i)) ^ 2 := by
  have hreaction : curvatureTensorReaction3 K12 K13 K23 =
      rm (ricciFromSectional3
        (sectionalReaction12 K12 K13 K23)
        (sectionalReaction13 K12 K13 K23)
        (sectionalReaction23 K12 K13 K23)) := by
    funext a b c d
    exact curvatureTensorReaction3_eq_rm K12 K13 K23 a b c d
  rw [hreaction, curvatureOperatorQuadraticEval3_rm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction ``Submission.DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction

theorem curvatureOperatorQuadraticEval3_reaction_nonneg {n : Nat}
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (c : Fin n → Real) (v w : Fin n → Fin 3 → Real) :
    0 ≤ curvatureOperatorQuadraticEval3
      (curvatureTensorReaction3 K12 K13 K23) c v w := by
  rw [curvatureOperatorQuadraticEval3_reaction]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (sectionalReaction12_nonneg K12 K13 K23 h13 h23) (sq_nonneg _))
      (mul_nonneg (sectionalReaction13_nonneg K12 K13 K23 h12 h23) (sq_nonneg _)))
    (mul_nonneg (sectionalReaction23_nonneg K12 K13 K23 h12 h13) (sq_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction_nonneg ``Submission.DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction_nonneg

end DifferentialGeometry.Dim3Reaction
