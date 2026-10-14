import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
import Submission.DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSingularCycleMap (n : ℕ) (f : C(X, Y)) :
    integralSingularCycles n X →ₗ[ℤ] integralSingularCycles n Y :=
  moduleCycleMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleMap ``Submission.DifferentialGeometry.Topology.integralSingularCycleMap

@[simp]
theorem integralSingularCycleMap_val (n : ℕ) (f : C(X, Y))
    (z : integralSingularCycles n X) :
    (integralSingularCycleMap n f z).val = (integralSingularChainMap f).f (n + 1) z.val :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleMap_val ``Submission.DifferentialGeometry.Topology.integralSingularCycleMap_val

private theorem integralSingularCycleClass_eq (n : ℕ) (z : integralSingularCycles n X) :
    integralSingularCycleClass n X z =
      ((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z) := by
  apply (integralSingularHomologyCycleEquiv n X).injective
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply]
  change _ = ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatHomologyIso.hom
    (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
      (by simp) (by simp)).hom
      (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv _))
  rw [Iso.inv_hom_id_apply]
  exact (moduleHomologyClass_quotient
    ((integralSingularChains X).sc' (n + 2) (n + 1) n) z).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCycleClass_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCycleClass_eq target :: scope.openDecls } }

theorem integralSingularCycleClass_map (n : ℕ) (f : C(X, Y))
    (z : integralSingularCycles n X) :
    integralSingularHomologyMap (n + 1) f (integralSingularCycleClass n X z) =
      integralSingularCycleClass n Y (integralSingularCycleMap n f z) := by
  rw [integralSingularCycleClass_eq, integralSingularCycleClass_eq]
  let e := HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (n + 2) (n + 1) n (by simp) (by simp)
  have h := congrArg (fun g => g
    (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z))
    (e.inv.naturality (integralSingularChainMap f))
  change ((integralSingularChains Y).homologyIsoSc' (n + 2) (n + 1) n
    (by simp) (by simp)).inv
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
          (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f))
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z)) =
    integralSingularHomologyMap (n + 1) f
      (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z)) at h
  exact h.symm.trans (congrArg
    ((integralSingularChains Y).homologyIsoSc' (n + 2) (n + 1) n
      (by simp) (by simp)).inv
    (moduleHomologyClass_map
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
        (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f)) z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClass_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClass_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClass_map ``Submission.DifferentialGeometry.Topology.integralSingularCycleClass_map

end DifferentialGeometry.Topology
