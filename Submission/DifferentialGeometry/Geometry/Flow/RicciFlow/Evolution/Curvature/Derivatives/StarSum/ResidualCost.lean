import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.TimeRecursion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.ResidualDecomposition
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

def rmTowerCost (d k : ℕ) : Real :=
  2 * Real.sqrt (Fintype.card (Fin (4 + k) -> Fin d) : Real) *
    (((4 + k : Nat) : Real) * (d : Real) ^ 2 + rmResidualCost d k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmTowerCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmTowerCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmTowerCost ``Submission.DifferentialGeometry.PDE.RicciFlow.rmTowerCost

theorem rmTowerCost_nonneg (d k : ℕ) :
    0 ≤ rmTowerCost d k := by
  have hres := rmResidualCost_nonneg d k
  unfold rmTowerCost
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmTowerCost_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmTowerCost_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmTowerCost_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.rmTowerCost_nonneg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem e0Field_cost_any {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    StarSum2Cost (I := I) Idx S t 0 (e0Field (I := I) S t)
      (12 * (Fintype.card Idx : Real) ^ 2) := by
  unfold e0Field
  convert StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
    (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 btPermE))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt2)))
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 σBt3)))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt4)))
      (StarSum2Cost.base 0 0 0 0 σD1))
      (StarSum2Cost.base 0 0 0 0 σD2))
      (StarSum2Cost.base 0 0 0 0 σD3))
      (StarSum2Cost.base 0 0 0 0 σD4) using 1
  all_goals ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.e0Field_cost_any then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.e0Field_cost_any"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.e0Field_cost_any ``Submission.DifferentialGeometry.PDE.RicciFlow.e0Field_cost_any

def rmBaseReact {Idx : Type*} [Fintype Idx]
    (R : (Fin 4 -> Idx) -> Real) (m : Fin 4 -> Idx) : Real :=
  DifferentialGeometry.Geometry.Connection.hamiltonRmReact R m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmBaseReact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmBaseReact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmBaseReact ``Submission.DifferentialGeometry.PDE.RicciFlow.rmBaseReact

omit [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem e0Field_comp_any {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (m : Fin 4 -> Idx) :
    e0Field (I := I) S t x (fun p => basis (m p)) =
      rmBaseReact
        (fun q => nablaKRm04Field (I := I) S t 0 x (fun p => basis (q p))) m := by
  have hev :
      e0Field (I := I) S t x (fun p => basis (m p)) =
        -2 * starBaseField (I := I) S t 0 0 0 0 btPermE x (fun p => basis (m p))
          + 2 * starBaseField (I := I) S t 0 0 0 0 σBt2 x (fun p => basis (m p))
          + -2 * starBaseField (I := I) S t 0 0 0 0 σBt3 x (fun p => basis (m p))
          + 2 * starBaseField (I := I) S t 0 0 0 0 σBt4 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD1 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD2 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD3 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD4 x (fun p => basis (m p)) := rfl
  rw [hev, btStar_eq (I := I) S t basis horth m,
    btStar2 (I := I) S t basis horth m, btStar3 (I := I) S t basis horth m,
    btStar4 (I := I) S t basis horth m, drStar1 (I := I) S t basis horth m,
    drStar2 (I := I) S t basis horth m, drStar3 (I := I) S t basis horth m,
    drStar4 (I := I) S t basis horth m]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.e0Field_comp_any then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.e0Field_comp_any"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.e0Field_comp_any ``Submission.DifferentialGeometry.PDE.RicciFlow.e0Field_comp_any

theorem rmGammaCost_three (k : ℕ) :
    rmGammaCost 3 k = gammaStarCost k := by
  norm_num [rmGammaCost, gammaStarCost]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmGammaCost_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmGammaCost_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmGammaCost_three ``Submission.DifferentialGeometry.PDE.RicciFlow.rmGammaCost_three

theorem rmResidualCost_three (k : ℕ) :
    rmResidualCost 3 k = resStarCost k := by
  induction k with
  | zero => norm_num [rmResidualCost, resStarCost]
  | succ k ih =>
      simp only [rmResidualCost, resStarCost]
      rw [ih, rmGammaCost_three]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmResidualCost_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmResidualCost_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmResidualCost_three ``Submission.DifferentialGeometry.PDE.RicciFlow.rmResidualCost_three

end DifferentialGeometry.PDE.RicciFlow
