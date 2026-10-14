import Submission.DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeComponents
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.Higher
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators

section ComponentRecursion

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def iteratedRmComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) :
    (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real
  | 0 => base
  | (k + 1) => fun t x =>
      covDerivStepComp
        (frameDirectionalDerivatives (I := I) frame
          (fun y : M => iteratedRmComp frame chr base k t y) x)
        (chr t x)
        (iteratedRmComp frame chr base k t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iteratedRmComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp ``Submission.DifferentialGeometry.PDE.RicciFlow.iteratedRmComp

omit [DecidableEq Idx] in
@[simp] theorem iteratedRmComp_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) :
    iteratedRmComp (I := I) frame chr base 0 = base := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_zero

omit [DecidableEq Idx] in
theorem iteratedRmComp_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) (k : ℕ) (t : Real) (x : M) :
    iteratedRmComp (I := I) frame chr base (k + 1) t x =
      covDerivStepComp
        (frameDirectionalDerivatives (I := I) frame
          (fun y : M => iteratedRmComp (I := I) frame chr base k t y) x)
        (chr t x)
        (iteratedRmComp (I := I) frame chr base k t x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_succ ``Submission.DifferentialGeometry.PDE.RicciFlow.iteratedRmComp_succ

end ComponentRecursion

section OrthonormalReduction

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def multiNormRaised {r : ℕ}
    (gInv : Idx → Idx → Real) (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, ∑ n : Fin r → Idx,
    (∏ s : Fin r, gInv (m s) (n s)) * A m * A n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.multiNormRaised then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.multiNormRaised"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.multiNormRaised ``Submission.DifferentialGeometry.PDE.RicciFlow.multiNormRaised

omit [Fintype Idx] in
theorem prod_delta_eq {r : ℕ} (m n : Fin r → Idx) :
    (∏ s : Fin r, (if m s = n s then (1 : Real) else 0)) =
      (if m = n then 1 else 0) := by
  classical
  by_cases h : m = n
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [if_neg hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.prod_delta_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.prod_delta_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.prod_delta_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.prod_delta_eq

theorem multiNormInFrame_eq_compNormSqMulti {r : ℕ}
    (gInv : Idx → Idx → Real)
    (A : (Fin r → Idx) → Real)
    (horth : ∀ i j : Idx, gInv i j = if i = j then 1 else 0) :
    multiNormRaised (r := r) gInv A = compNormSqMulti A := by
  classical
  unfold multiNormRaised compNormSqMulti
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m]
  · have hprod : (∏ s : Fin r, gInv (m s) (m s)) = 1 := by
      refine Finset.prod_eq_one fun s _ => ?_
      rw [horth (m s) (m s), if_pos rfl]
    rw [hprod]; ring
  · intro n _ hn
    have hprod : (∏ s : Fin r, gInv (m s) (n s)) = 0 := by
      have : (∏ s : Fin r, gInv (m s) (n s)) =
          ∏ s : Fin r, (if m s = n s then (1 : Real) else 0) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [horth (m s) (n s)]
      rw [this, prod_delta_eq, if_neg (fun h => hn h.symm)]
    rw [hprod]; ring
  · intro h; exact absurd (Finset.mem_univ m) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.multiNormInFrame_eq_compNormSqMulti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.multiNormInFrame_eq_compNormSqMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.multiNormInFrame_eq_compNormSqMulti ``Submission.DifferentialGeometry.PDE.RicciFlow.multiNormInFrame_eq_compNormSqMulti

end OrthonormalReduction

section TowerHeatInequality

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def towerReactionMulti
    (level : (k : ℕ) → (Fin (4 + k) → Idx) → Real)
    (star : (k : ℕ) → ℕ → (Fin (4 + k) → Idx) → Real)
    (k : ℕ) : Real :=
  nablaRmReactionMulti (level k) (star k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.towerReactionMulti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.towerReactionMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.towerReactionMulti ``Submission.DifferentialGeometry.PDE.RicciFlow.towerReactionMulti

structure IteratedRmTowerOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real)
    (star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real)
    (w wLap : ℕ → Real → M → Real) : Prop where
  wDef : ∀ (k : ℕ) (t : Real) (x : M),
    w k t x = compNormSqMulti (level k t x)

  heatEq : ∀ (k : ℕ)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M),
    HasDerivWithinAt (fun s : Real => w k s x)
      (wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x +
          towerReactionMulti (level · (t : Real) x) (star · (t : Real) x) k))
      D.carrier (t : Real)

  starBound : ∀ (k : ℕ) (t : Real) (x : M),
    ∀ j ∈ Finset.range (k + 1), ∀ m : Fin (4 + k) → Idx,
      |star k t x j m| ≤
        (Fintype.card Idx : Real) ^ 2 *
          (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IteratedRmTowerOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IteratedRmTowerOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IteratedRmTowerOn ``Submission.DifferentialGeometry.PDE.RicciFlow.IteratedRmTowerOn

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem abs_towerReactionMulti_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ) (t : Real) (x : M) :
    |towerReactionMulti (level · t x) (star · t x) k| ≤
      ∑ j ∈ Finset.range (k + 1),
        (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) := by
  unfold towerReactionMulti
  refine abs_nablaRmReactionMulti_le (level k t x) (star k t x) (fun j => w j t x) ?_ ?_
  · exact (T.wDef k t x).symm
  · intro j hj m
    exact T.starBound k t x j hj m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.abs_towerReactionMulti_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.abs_towerReactionMulti_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.abs_towerReactionMulti_le ``Submission.DifferentialGeometry.PDE.RicciFlow.abs_towerReactionMulti_le

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem iteratedRmTower_heatBoundSharp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    ∃ d : Real,
      HasDerivWithinAt (fun s : Real => w k s x) d D.carrier (t : Real) ∧
      d ≤ wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x +
          towerReactionSum (M := M) w (2 * (Fintype.card Idx : Real) ^ (6 + k))
            k (t : Real) x) := by
  refine ⟨_, T.heatEq k t x, ?_⟩
  have hreact_le :
      towerReactionMulti (level · (t : Real) x) (star · (t : Real) x) k ≤
        towerReactionSum (M := M) w (2 * (Fintype.card Idx : Real) ^ (6 + k))
          k (t : Real) x := by
    refine le_trans (le_abs_self _) ?_
    refine le_trans (abs_towerReactionMulti_le T k (t : Real) x) ?_
    unfold towerReactionSum
    apply le_of_eq
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith [hreact_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBoundSharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBoundSharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBoundSharp ``Submission.DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBoundSharp

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem iteratedRmTower_heatBound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ) :
    TowerHeatBoundOn (D := D) w wLap
      (2 * (Fintype.card Idx : Real) ^ (6 + k)) k := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ := iteratedRmTower_heatBoundSharp T k t x
  exact ⟨d, hderiv, hle⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBound ``Submission.DifferentialGeometry.PDE.RicciFlow.iteratedRmTower_heatBound

end TowerHeatInequality

end DifferentialGeometry.PDE.RicciFlow
