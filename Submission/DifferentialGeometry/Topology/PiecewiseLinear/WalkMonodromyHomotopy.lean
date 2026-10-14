/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CocycleWalkLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Set _root_.SimpleGraph

def closedWalkPow {V : Type*} {G : SimpleGraph V} {u : V} (γ : G.Walk u u) :
    ℕ → G.Walk u u
  | 0 => Walk.nil
  | k + 1 => γ.append (closedWalkPow γ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedWalkPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedWalkPow

def closedWalkZPow {V : Type*} {G : SimpleGraph V} {u : V} (γ : G.Walk u u) : ℤ → G.Walk u u
  | Int.ofNat k => closedWalkPow γ k
  | Int.negSucc k => closedWalkPow γ.reverse (k + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow

theorem closedWalkZPow_natCast {V : Type*} {G : SimpleGraph V} {u : V} (γ : G.Walk u u) (k : ℕ) :
    closedWalkZPow γ (k : ℤ) = closedWalkPow γ k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_natCast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_natCast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_natCast ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_natCast

theorem closedWalkZPow_negSucc {V : Type*} {G : SimpleGraph V} {u : V} (γ : G.Walk u u) (k : ℕ) :
    closedWalkZPow γ (Int.negSucc k) = closedWalkPow γ.reverse (k + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_negSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_negSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_negSucc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedWalkZPow_negSucc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

theorem walkMonodromy_closedWalkPow {u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk u u) (k : ℕ) :
    ε.walkMonodromy (closedWalkPow γ k) = (k : ZMod 2) * ε.walkMonodromy γ := by
  induction k with
  | zero => rw [closedWalkPow, ε.walkMonodromy_nil, Nat.cast_zero, _root_.MulZeroClass.zero_mul]
  | succ k ih =>
      rw [closedWalkPow, ε.walkMonodromy_append, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkPow

theorem walkMonodromy_closedWalkZPow {u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk u u) (k : ℤ) :
    ε.walkMonodromy (closedWalkZPow γ k) = (k : ZMod 2) * ε.walkMonodromy γ := by
  cases k with
  | ofNat k =>
      have hk : (Int.ofNat k) = (k : ℤ) := rfl
      rw [hk, closedWalkZPow_natCast, ε.walkMonodromy_closedWalkPow, Int.cast_natCast]
  | negSucc k =>
      rw [closedWalkZPow_negSucc, ε.walkMonodromy_closedWalkPow, ε.walkMonodromy_reverse]
      rw [show ((Int.negSucc k : ℤ) : ZMod 2) = ((k + 1 : ℕ) : ZMod 2) by
        rw [Int.negSucc_eq]
        push_cast
        ring_nf
        exact CharTwo.sub_eq_add _ _]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkZPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_closedWalkZPow

theorem walkMonodromy_conjugate {u v : K.vertices}
    (q : (SimplicialComplex.edgeGraph K).Walk u v)
    (r : (SimplicialComplex.edgeGraph K).Walk v v) :
    ε.walkMonodromy (q.append (r.append q.reverse)) = ε.walkMonodromy r := by
  rw [ε.walkMonodromy_append, ε.walkMonodromy_append, ε.walkMonodromy_reverse,
    add_comm (ε.walkMonodromy r), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_conjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_conjugate

variable [FiniteDimensional ℝ E] [Finite K.faces]

open _root_.Classical in
theorem walkParity_eq_of_homotopic {u w : K.vertices}
    (p q : (SimplicialComplex.edgeGraph K).Walk u w)
    (hpq : (walkPath p).Homotopic (walkPath q)) :
    ε.walkParity p = ε.walkParity q := by
  obtain ⟨Γp, hΓp⟩ := ε.exists_walkLift p _root_.Bool.false
  obtain ⟨Γq, hΓq⟩ := ε.exists_walkLift q _root_.Bool.false
  have h0 : (walkPath p).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    (walkPath p).source
  have h1 : (walkPath q).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    (walkPath q).source
  have hliftp : Γp.toContinuousMap =
      ε.isCoveringMap.liftPath (walkPath p).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 :=
    (ε.isCoveringMap.eq_liftPath_iff' h0).mpr ⟨funext fun t => hΓp t, Γp.source⟩
  have hliftq : Γq.toContinuousMap =
      ε.isCoveringMap.liftPath (walkPath q).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h1 :=
    (ε.isCoveringMap.eq_liftPath_iff' h1).mpr ⟨funext fun t => hΓq t, Γq.source⟩
  have hsame := ε.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel hpq
    (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 h1
  have hval : Γp.toContinuousMap 1 = Γq.toContinuousMap 1 := by
    rw [hliftp, hliftq, hsame]
  have hend := Γp.target.symm.trans (hval.trans Γq.target)
  have hbool := Bundle.TotalSpace.mk_inj.mp hend
  rwa [Bool.false_xor, Bool.false_xor] at hbool

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkParity_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkParity_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkParity_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkParity_eq_of_homotopic

open _root_.Classical in
theorem walkMonodromy_eq_of_homotopic {u w : K.vertices}
    (p q : (SimplicialComplex.edgeGraph K).Walk u w)
    (hpq : (walkPath p).Homotopic (walkPath q)) :
    ε.walkMonodromy p = ε.walkMonodromy q := by
  rw [← ε.boolZMod2_walkParity p, ← ε.boolZMod2_walkParity q,
    ε.walkParity_eq_of_homotopic p q hpq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_homotopic

open _root_.Classical in
theorem walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow {v₀ u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph K).Walk u u)
    (q : (SimplicialComplex.edgeGraph K).Walk u v₀) (k : ℤ)
    (hp : (walkPath p).Homotopic
      (walkPath (q.append ((closedWalkZPow γ k).append q.reverse)))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_homotopic p _ hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkZPow]
  rcases hx ((k : ZMod 2)) with hk | hk
  · exact Or.inl (by rw [hk, _root_.MulZeroClass.zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow

open _root_.Classical in
theorem walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow {v₀ u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph K).Walk u u)
    (q : (SimplicialComplex.edgeGraph K).Walk u v₀) (k : ℕ)
    (hp : (walkPath p).Homotopic
      (walkPath (q.append ((closedWalkPow γ k).append q.reverse)))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_homotopic p _ hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkPow]
  rcases hx (k : ZMod 2) with hk | hk
  · exact Or.inl (by rw [hk, _root_.MulZeroClass.zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
