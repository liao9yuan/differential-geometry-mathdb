import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual homology under homotopy equivalences and contractions -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original continuous homotopy equivalence induces inverse maps of
the original integral singular homology groups. -/
def integralSingularHomologyHomotopyEquiv (n : ℕ) (e : X ≃ₕ Y) :
    integralSingularHomology n X ≃ₗ[ℤ] integralSingularHomology n Y where
  toLinearMap := integralSingularHomologyMap n e.toFun
  invFun := integralSingularHomologyMap n e.invFun
  left_inv a := by
    have h := (integralSingularHomologyMap_comp n e.toFun e.invFun).symm.trans
      ((integralSingularHomologyMap_homotopic n e.left_inv).trans (integralSingularHomologyMap_id n))
    exact LinearMap.congr_fun h a
  right_inv a := by
    have h := (integralSingularHomologyMap_comp n e.invFun e.toFun).symm.trans
      ((integralSingularHomologyMap_homotopic n e.right_inv).trans (integralSingularHomologyMap_id n))
    exact LinearMap.congr_fun h a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv ``Submission.DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv

/-- The actual positive-degree homology vanishes on totally disconnected
spaces, using the pinned alternating constant-complex computation. -/
theorem integralSingularHomology_subsingleton_of_totallyDisconnected (n : ℕ) (hn : n ≠ 0)
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    Subsingleton (integralSingularHomology n X) :=
  ModuleCat.subsingleton_of_isZero
    (_root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} ℤ) n
      integralSingularCoefficients (TopCat.of X) hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_totallyDisconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_totallyDisconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_totallyDisconnected ``Submission.DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_totallyDisconnected

/-- A constant original map induces the zero map in positive homological
degree, by its actual factorization through a one-point space. -/
theorem integralSingularHomologyMap_const (n : ℕ) (hn : n ≠ 0) (y : Y) :
    integralSingularHomologyMap n (ContinuousMap.const X y) = 0 := by
  let f : C(X, PUnit.{u + 1}) := .const X PUnit.unit
  let g : C(PUnit.{u + 1}, Y) := .const _ y
  let := integralSingularHomology_subsingleton_of_totallyDisconnected n hn PUnit.{u + 1}
  have h : ContinuousMap.const X y = g.comp f := rfl
  rw [h, integralSingularHomologyMap_comp]
  ext a
  have ha : integralSingularHomologyMap n f a = 0 := Subsingleton.elim _ _
  simp only [LinearMap.comp_apply, ha, map_zero, LinearMap.zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_const ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_const

/-- An actual nullhomotopy annihilates the induced positive-degree map. -/
theorem integralSingularHomologyMap_nullhomotopic (n : ℕ) (hn : n ≠ 0)
    {f : C(X, Y)} (h : f.Nullhomotopic) : integralSingularHomologyMap n f = 0 := by
  obtain ⟨y, hy⟩ := h
  exact (integralSingularHomologyMap_homotopic n hy).trans
    (integralSingularHomologyMap_const n hn y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_nullhomotopic ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_nullhomotopic

/-- Contractibility kills the actual positive-degree singular homology,
without defining homology to be zero on such spaces. -/
theorem integralSingularHomology_subsingleton_of_contractible (n : ℕ) (hn : n ≠ 0)
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    Subsingleton (integralSingularHomology n X) := by
  have h := (integralSingularHomologyMap_id (X := X) n).symm.trans
    (integralSingularHomologyMap_nullhomotopic n hn (id_nullhomotopic X))
  have hz : ∀ a : integralSingularHomology n X, a = 0 := fun a => LinearMap.congr_fun h a
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible ``Submission.DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible

end DifferentialGeometry.Topology
