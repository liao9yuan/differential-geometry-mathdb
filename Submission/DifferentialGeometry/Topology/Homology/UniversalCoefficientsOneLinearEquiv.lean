import Submission.DifferentialGeometry.Topology.Homology.CycleLinearEquiv
import Submission.DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

private def zLinearMapOfAddMonoidHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [mM : Module ℤ M] [mN : Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' m x := by
    change f (mM.smul m x) = mN.smul m (f x)
    rw [int_smul_eq_zsmul mM m x, int_smul_eq_zsmul mN m (f x)]
    exact f.map_zsmul m x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.zLinearMapOfAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.zLinearMapOfAddMonoidHom target :: scope.openDecls } }
variable {X : Type u} [TopologicalSpace X]
def integralSingularCocycleClass (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCocycles n X) : integralSingularCohomology (n + 1) X :=
  (integralSingularCohomologyCycleLinearEquiv n X).symm (Submodule.Quotient.mk z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass

private def integralSingularCocycleClassAddMonoidHom (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCocycles n X →+ integralSingularCohomology (n + 1) X :=
  (((integralSingularCohomologyCycleLinearEquiv n X).symm).toAddEquiv.toAddMonoidHom).comp
    (Submodule.mkQ (LinearMap.range (integralSingularCoboundaryToCycles n X))).toAddMonoidHom

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClassAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCocycleClassAddMonoidHom target :: scope.openDecls } }

theorem integralSingularCocycleClass_add (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z z' : integralSingularCocycles n X) :
    integralSingularCocycleClass n X (z + z') =
      integralSingularCocycleClass n X z + integralSingularCocycleClass n X z' :=
  map_add (integralSingularCocycleClassAddMonoidHom n X) z z'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass_add ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass_add

def integralSingularCocycleClassLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCocycles n X →ₗ[ℤ] integralSingularCohomology (n + 1) X :=
  zLinearMapOfAddMonoidHom (integralSingularCocycleClassAddMonoidHom n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap

theorem integralSingularCocycleClassLinearMap_apply (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCocycles n X) :
    integralSingularCocycleClassLinearMap n X z = integralSingularCocycleClass n X z :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap_apply ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClassLinearMap_apply

theorem integralSingularCocycleClass_coboundary (n : ℕ) (X : Type u) [TopologicalSpace X]
    (c : integralSingularCochain n X) :
    integralSingularCocycleClass n X (integralSingularCoboundaryToCycles n X c) = 0 := by
  rw [integralSingularCocycleClass, LinearEquiv.symm_apply_eq, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass_coboundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass_coboundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass_coboundary ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass_coboundary

theorem integralSingularCocycleClass_surjective (n : ℕ) (X : Type u) [TopologicalSpace X]
    (y : integralSingularCohomology (n + 1) X) :
    ∃ z : integralSingularCocycles n X, integralSingularCocycleClass n X z = y := by
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
    (LinearMap.range (integralSingularCoboundaryToCycles n X))
    ((integralSingularCohomologyCycleLinearEquiv n X) y)
  refine ⟨z, ?_⟩
  rw [integralSingularCocycleClass, Submodule.mkQ_apply] at *
  rw [hz, LinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass_surjective ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass_surjective

theorem integralSingularCocycleClass_eq_zero_iff (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCocycles n X) :
    integralSingularCocycleClass n X z = 0 ↔
      ∃ c : integralSingularCochain n X, integralSingularCoboundaryToCycles n X c = z := by
  constructor
  · intro h
    rw [integralSingularCocycleClass, LinearEquiv.symm_apply_eq, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · rintro ⟨c, rfl⟩
    exact integralSingularCocycleClass_coboundary n X c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass_eq_zero_iff ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass_eq_zero_iff

private def integralSingularCycleClassAddMonoidHom (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCycles n X →+ integralSingularHomology (n + 1) X :=
  (((integralSingularHomologyCycleEquiv n X).symm).toAddMonoidHom).comp
    (Submodule.mkQ (LinearMap.range (integralSingularBoundaryToCycles n X))).toAddMonoidHom

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCycleClassAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCycleClassAddMonoidHom target :: scope.openDecls } }

def integralSingularCycleClassLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCycles n X →ₗ[ℤ] integralSingularHomology (n + 1) X :=
  zLinearMapOfAddMonoidHom (integralSingularCycleClassAddMonoidHom n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClassLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap ``Submission.DifferentialGeometry.Topology.integralSingularCycleClassLinearMap

theorem integralSingularCycleClassLinearMap_apply (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCycles n X) :
    integralSingularCycleClassLinearMap n X z = integralSingularCycleClass n X z :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_apply ``Submission.DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_apply

theorem integralSingularCoboundaryToCycles_coe (n : ℕ) (X : Type u) [TopologicalSpace X]
    (c : integralSingularCochain n X) :
    (integralSingularCoboundaryToCycles n X c).1 =
      integralSingularCoboundary X n (n + 1) c :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCoboundaryToCycles_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCoboundaryToCycles_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCoboundaryToCycles_coe ``Submission.DifferentialGeometry.Topology.integralSingularCoboundaryToCycles_coe

theorem integralSingularCycleClassLinearMap_boundary (n : ℕ) (X : Type u) [TopologicalSpace X]
    (c : (integralSingularChains X).X (n + 2)) :
    integralSingularCycleClassLinearMap n X (integralSingularBoundaryToCycles n X c) = 0 := by
  rw [integralSingularCycleClassLinearMap_apply]
  exact integralSingularCycleClass_boundary n X c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_boundary ``Submission.DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_boundary

theorem integralSingularCycleClassLinearMap_surjective (n : ℕ) (X : Type u)
    [TopologicalSpace X] (y : integralSingularHomology (n + 1) X) :
    ∃ z : integralSingularCycles n X, integralSingularCycleClassLinearMap n X z = y := by
  obtain ⟨z, hz⟩ := integralSingularCycleClass_surjective n X y
  exact ⟨z, by rw [integralSingularCycleClassLinearMap_apply, hz]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_surjective ``Submission.DifferentialGeometry.Topology.integralSingularCycleClassLinearMap_surjective

def integralCycleFunctionalSubmodule (X : Type u) [TopologicalSpace X] :
    Submodule ℤ (integralSingularCycles 0 X →ₗ[ℤ] ℤ) where
  carrier := {g | ∀ c : (integralSingularChains X).X 2,
    g (integralSingularBoundaryToCycles 0 X c) = 0}
  zero_mem' := by
    intro c
    rw [LinearMap.zero_apply]
  add_mem' := by
    intro g h hg hh c
    rw [LinearMap.add_apply, hg c, hh c, add_zero]
  smul_mem' := by
    intro a g hg c
    rw [LinearMap.smul_apply, hg c, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalSubmodule ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalSubmodule

theorem integralCocycleOfCycleFunctional_add [PathConnectedSpace X] (a : X)
    (g h : integralSingularCycles 0 X →ₗ[ℤ] ℤ) :
    integralCocycleOfCycleFunctional a (g + h) =
      integralCocycleOfCycleFunctional a g + integralCocycleOfCycleFunctional a h := by
  change (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
      ((g + h).comp (integralCycleRetraction a)) =
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
        (g.comp (integralCycleRetraction a)) +
      (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
        (h.comp (integralCycleRetraction a))
  rw [LinearMap.add_comp, LinearMap.comp_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_add ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_add

theorem integralCocycleOfCycleFunctional_zero [PathConnectedSpace X] (a : X) :
    integralCocycleOfCycleFunctional a 0 = 0 := by
  change (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
    ((0 : integralSingularCycles 0 X →ₗ[ℤ] ℤ).comp (integralCycleRetraction a)) = 0
  rw [LinearMap.zero_comp, LinearMap.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_zero ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctional_zero

def integralCocycleOfCycleFunctionalOnCycles [PathConnectedSpace X] (a : X)
    (g : ↥(integralCycleFunctionalSubmodule X)) : integralSingularCocycles 0 X :=
  ⟨integralCocycleOfCycleFunctional a g.1,
    integralCocycleOfCycleFunctional_cocycle a g.1 fun c => g.2 c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles

theorem integralCocycleOfCycleFunctionalOnCycles_coe [PathConnectedSpace X] (a : X)
    (g : ↥(integralCycleFunctionalSubmodule X)) :
    (integralCocycleOfCycleFunctionalOnCycles a g).1 =
      integralCocycleOfCycleFunctional a g.1 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_coe ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_coe

theorem integralCocycleOfCycleFunctionalOnCycles_evaluation [PathConnectedSpace X] (a : X)
    (g : ↥(integralCycleFunctionalSubmodule X)) (z : integralSingularCycles 0 X) :
    integralCocycleEvaluation 0 (integralCocycleOfCycleFunctionalOnCycles a g).1 z = g.1 z :=
  integralCocycleEvaluation_cycleFunctional a g.1 z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_evaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_evaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_evaluation ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_evaluation

theorem integralCocycleOfCycleFunctionalOnCycles_add [PathConnectedSpace X] (a : X)
    (g h : ↥(integralCycleFunctionalSubmodule X)) :
    integralCocycleOfCycleFunctionalOnCycles a (g + h) =
      integralCocycleOfCycleFunctionalOnCycles a g +
        integralCocycleOfCycleFunctionalOnCycles a h := by
  apply Subtype.ext
  change integralCocycleOfCycleFunctional a (g + h).1 =
    integralCocycleOfCycleFunctional a g.1 + integralCocycleOfCycleFunctional a h.1
  rw [Submodule.coe_add, integralCocycleOfCycleFunctional_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_add ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_add

theorem integralCocycleOfCycleFunctionalOnCycles_zero [PathConnectedSpace X] (a : X) :
    integralCocycleOfCycleFunctionalOnCycles a 0 = 0 := by
  apply Subtype.ext
  change integralCocycleOfCycleFunctional a (0 : integralSingularCycles 0 X →ₗ[ℤ] ℤ) = 0
  rw [integralCocycleOfCycleFunctional_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_zero ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCycles_zero

private def integralCocycleOfCycleFunctionalOnCyclesAddMonoidHom [PathConnectedSpace X] (a : X) :
    ↥(integralCycleFunctionalSubmodule X) →+ integralSingularCocycles 0 X where
  toFun := integralCocycleOfCycleFunctionalOnCycles a
  map_zero' := integralCocycleOfCycleFunctionalOnCycles_zero a
  map_add' := integralCocycleOfCycleFunctionalOnCycles_add a

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCyclesAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralCocycleOfCycleFunctionalOnCyclesAddMonoidHom target :: scope.openDecls } }

def integralCycleFunctionalOfHomology [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) : ↥(integralCycleFunctionalSubmodule X) :=
  ⟨g.comp (integralSingularCycleClassLinearMap 0 X), fun c => by
    rw [LinearMap.comp_apply, integralSingularCycleClassLinearMap_boundary 0 X c, map_zero]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalOfHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomology

theorem integralCycleFunctionalOfHomology_coe [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) :
    (integralCycleFunctionalOfHomology g).1 =
      g.comp (integralSingularCycleClassLinearMap 0 X) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_coe ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_coe

theorem integralCycleFunctionalOfHomology_apply [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) (z : integralSingularCycles 0 X) :
    (integralCycleFunctionalOfHomology g).1 z =
      g (integralSingularCycleClassLinearMap 0 X z) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_apply ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_apply

theorem integralCycleFunctionalOfHomology_add [PathConnectedSpace X]
    (g h : integralSingularHomology 1 X →ₗ[ℤ] ℤ) :
    integralCycleFunctionalOfHomology (g + h) =
      integralCycleFunctionalOfHomology g + integralCycleFunctionalOfHomology h := by
  apply Subtype.ext
  change (g + h).comp (integralSingularCycleClassLinearMap 0 X) =
    g.comp (integralSingularCycleClassLinearMap 0 X) +
      h.comp (integralSingularCycleClassLinearMap 0 X)
  rw [LinearMap.add_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_add ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_add

theorem integralCycleFunctionalOfHomology_zero [PathConnectedSpace X] :
    integralCycleFunctionalOfHomology (0 : integralSingularHomology 1 X →ₗ[ℤ] ℤ) = 0 := by
  apply Subtype.ext
  change (0 : integralSingularHomology 1 X →ₗ[ℤ] ℤ).comp
    (integralSingularCycleClassLinearMap 0 X) = 0
  rw [LinearMap.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_zero ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomology_zero

private def integralCycleFunctionalOfHomologyAddMonoidHom [PathConnectedSpace X] :
    (integralSingularHomology 1 X →ₗ[ℤ] ℤ) →+ ↥(integralCycleFunctionalSubmodule X) where
  toFun := integralCycleFunctionalOfHomology
  map_zero' := integralCycleFunctionalOfHomology_zero
  map_add' := integralCycleFunctionalOfHomology_add

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralCycleFunctionalOfHomologyAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralCycleFunctionalOfHomologyAddMonoidHom target :: scope.openDecls } }

private def integralCohomologyOneEvaluationAddMonoidHom [PathConnectedSpace X] :
    (integralSingularHomology 1 X →ₗ[ℤ] ℤ) →+ integralSingularCohomology 1 X :=
  (integralSingularCocycleClassAddMonoidHom 0 X).comp
    ((integralCocycleOfCycleFunctionalOnCyclesAddMonoidHom
        (Classical.choice (inferInstance : Nonempty X))).comp
      integralCycleFunctionalOfHomologyAddMonoidHom)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluationAddMonoidHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralCohomologyOneEvaluationAddMonoidHom target :: scope.openDecls } }

def integralCohomologyOneEvaluationLinearMap [PathConnectedSpace X] :
    (integralSingularHomology 1 X →ₗ[ℤ] ℤ) →ₗ[ℤ] integralSingularCohomology 1 X :=
  zLinearMapOfAddMonoidHom integralCohomologyOneEvaluationAddMonoidHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap

theorem integralCohomologyOneEvaluationLinearMap_apply [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) :
    integralCohomologyOneEvaluationLinearMap g =
      integralSingularCocycleClass 0 X
        (integralCocycleOfCycleFunctionalOnCycles
          (Classical.choice (inferInstance : Nonempty X))
          (integralCycleFunctionalOfHomology g)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply

theorem integralSingularCocycleClass_eq_of_evaluation_eq [PathConnectedSpace X]
    (φ ψ : integralSingularCocycles 0 X)
    (h : ∀ z : integralSingularCycles 0 X,
      integralCocycleEvaluation 0 φ.1 z = integralCocycleEvaluation 0 ψ.1 z) :
    integralSingularCocycleClass 0 X φ = integralSingularCocycleClass 0 X ψ := by
  let φ' : integralSingularCochain (0 + 1) X := φ.1
  let ψ' : integralSingularCochain (0 + 1) X := ψ.1
  let d : integralSingularCochain (0 + 1) X := φ' - ψ'
  have hd : ∀ z : integralSingularCycles 0 X, integralCocycleEvaluation 0 d z = 0 := by
    intro z
    have hz := h z
    rw [show integralCocycleEvaluation 0 φ' z = integralCocycleEvaluation 0 φ.1 z from rfl,
      show integralCocycleEvaluation 0 ψ' z = integralCocycleEvaluation 0 ψ.1 z from rfl] at hz
    rw [integralCocycleEvaluation_apply 0 φ' z,
      integralCocycleEvaluation_apply 0 ψ' z] at hz
    rw [integralCocycleEvaluation_apply 0 d z,
      show d z.1 = φ' z.1 - ψ' z.1 from rfl, map_sub, hz, sub_self]
  obtain ⟨c, hc⟩ := integralCocycle_eq_coboundary_of_evaluation_eq_zero d hd
  have hsub : φ - ψ = integralSingularCoboundaryToCycles 0 X c := by
    apply Subtype.ext
    rw [Submodule.coe_sub, integralSingularCoboundaryToCycles_coe, hc]
    rfl
  calc integralSingularCocycleClass 0 X φ
      = integralSingularCocycleClass 0 X (ψ + (φ - ψ)) := by rw [add_sub_cancel]
    _ = integralSingularCocycleClass 0 X ψ +
          integralSingularCocycleClass 0 X (φ - ψ) :=
        integralSingularCocycleClass_add 0 X ψ (φ - ψ)
    _ = integralSingularCocycleClass 0 X ψ := by
        rw [hsub, integralSingularCocycleClass_coboundary, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycleClass_eq_of_evaluation_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycleClass_eq_of_evaluation_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycleClass_eq_of_evaluation_eq ``Submission.DifferentialGeometry.Topology.integralSingularCocycleClass_eq_of_evaluation_eq

theorem integralCohomologyOneEvaluation_eq_zero_iff [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) :
    integralCohomologyOneEvaluationLinearMap g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have hκ : integralSingularCocycleClass 0 X
        (integralCocycleOfCycleFunctionalOnCycles
          (Classical.choice (inferInstance : Nonempty X))
          (integralCycleFunctionalOfHomology g)) = 0 := by
      rw [← integralCohomologyOneEvaluationLinearMap_apply]
      exact h
    obtain ⟨c, hc⟩ := (integralSingularCocycleClass_eq_zero_iff 0 X _).mp hκ
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := integralSingularCycleClassLinearMap_surjective 0 X y
    rw [LinearMap.zero_apply]
    have h2 : integralCocycleEvaluation 0
        (integralCocycleOfCycleFunctionalOnCycles
          (Classical.choice (inferInstance : Nonempty X))
          (integralCycleFunctionalOfHomology g)).1
        z = 0 := by
      rw [congrArg Subtype.val hc.symm]
      exact integralCoboundary_evaluation_apply c z
    rw [← integralCycleFunctionalOfHomology_apply g z,
      ← integralCocycleOfCycleFunctionalOnCycles_evaluation
        (Classical.choice (inferInstance : Nonempty X))
        (integralCycleFunctionalOfHomology g) z]
    exact h2
  · rintro rfl
    exact map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluation_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_eq_zero_iff ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluation_eq_zero_iff

theorem integralCohomologyOneEvaluation_injective [PathConnectedSpace X] :
    Function.Injective (integralCohomologyOneEvaluationLinearMap (X := X)) := by
  intro g h hgh
  have hsub : integralCohomologyOneEvaluationLinearMap (g - h) = 0 := by
    rw [map_sub, hgh, sub_self]
  have hz := (integralCohomologyOneEvaluation_eq_zero_iff (g - h)).mp hsub
  rwa [sub_eq_zero] at hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluation_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_injective ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluation_injective

theorem integralCohomologyOneEvaluation_surjective [PathConnectedSpace X] :
    Function.Surjective (integralCohomologyOneEvaluationLinearMap (X := X)) := by
  intro y
  obtain ⟨z₀, hz₀⟩ := integralSingularCocycleClass_surjective 0 X y
  let g₀ : integralSingularCycles 0 X →ₗ[ℤ] ℤ := integralCocycleEvaluation 0 z₀.1
  have hg₀ : ∀ c : (integralSingularChains X).X 2,
      g₀ (integralSingularBoundaryToCycles 0 X c) = 0 :=
    fun c => integralCocycleEvaluation_boundary 0 z₀.1 z₀.2 c
  have hker : LinearMap.range (integralSingularBoundaryToCycles 0 X) ≤ LinearMap.ker g₀ := by
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    exact hg₀ c
  let g₁ : (integralSingularCycles 0 X ⧸
      LinearMap.range (integralSingularBoundaryToCycles 0 X)) →ₗ[ℤ] ℤ :=
    Submodule.liftQ _ g₀ hker
  let gAdd : integralSingularHomology 1 X →+ ℤ :=
    (g₁.toAddMonoidHom).comp
      ((integralSingularHomologyCycleEquiv 0 X).toAddMonoidHom)
  let g : integralSingularHomology 1 X →ₗ[ℤ] ℤ := zLinearMapOfAddMonoidHom gAdd
  have hg₀' : ∀ z : integralSingularCycles 0 X,
      g (integralSingularCycleClass 0 X z) = g₀ z := by
    intro z
    change g₁ ((integralSingularHomologyCycleEquiv 0 X) (integralSingularCycleClass 0 X z)) =
      g₀ z
    rw [integralSingularCycleClass, AddEquiv.apply_symm_apply]
    change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 0 X)) g₀ hker)
      (Submodule.Quotient.mk z) = g₀ z
    rw [Submodule.liftQ_apply]
  obtain ⟨φ, hφc, hφ⟩ := exists_cocycle_evaluation_eq_of_forall_boundary_eq_zero g₀ hg₀
  refine ⟨g, ?_⟩
  rw [integralCohomologyOneEvaluationLinearMap_apply]
  rw [← hz₀]
  refine integralSingularCocycleClass_eq_of_evaluation_eq _ _ fun z => ?_
  rw [integralCocycleOfCycleFunctionalOnCycles_evaluation,
    integralCycleFunctionalOfHomology_apply]
  exact hg₀' z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluation_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluation_surjective ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluation_surjective

def integralSingularCohomologyOneLinearEquiv (X : Type u) [TopologicalSpace X]
    [PathConnectedSpace X] :
    ↑(integralSingularCohomology 1 X) ≃ₗ[ℤ] (integralSingularHomology 1 X →ₗ[ℤ] ℤ) :=
  (LinearEquiv.ofBijective (integralCohomologyOneEvaluationLinearMap (X := X))
    ⟨integralCohomologyOneEvaluation_injective,
      integralCohomologyOneEvaluation_surjective⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv

theorem integralSingularCohomologyOneLinearEquiv_symm [PathConnectedSpace X] :
    (integralSingularCohomologyOneLinearEquiv X).symm =
      integralCohomologyOneEvaluationLinearMap (X := X) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_symm ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_symm

theorem integralSingularCohomologyOneLinearEquiv_apply_evaluation [PathConnectedSpace X]
    (g : integralSingularHomology 1 X →ₗ[ℤ] ℤ) :
    integralSingularCohomologyOneLinearEquiv X (integralCohomologyOneEvaluationLinearMap g) = g :=
  LinearEquiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_apply_evaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_apply_evaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_apply_evaluation ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyOneLinearEquiv_apply_evaluation

theorem integralCohomologyOneEvaluationLinearMap_apply_linearEquiv [PathConnectedSpace X]
    (y : integralSingularCohomology 1 X) :
    integralCohomologyOneEvaluationLinearMap
      (integralSingularCohomologyOneLinearEquiv X y) = y := by
  rw [← integralSingularCohomologyOneLinearEquiv_symm]
  exact LinearEquiv.symm_apply_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply_linearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply_linearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply_linearEquiv ``Submission.DifferentialGeometry.Topology.integralCohomologyOneEvaluationLinearMap_apply_linearEquiv

end DifferentialGeometry.Topology
