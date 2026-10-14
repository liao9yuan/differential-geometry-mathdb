import Submission.DifferentialGeometry.Topology.Homotopy.OpenCollapse
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {Y : Type u}

theorem openCollapse_eq_of_mem {U : Set Y} {x y : Y} (hx : x ∈ U)
    (h : openCollapse U y = openCollapse U x) : y = x := by
  classical
  rw [show openCollapse U x = (⟨x, hx⟩ : U) from openCollapse_of_mem U ⟨x, hx⟩] at h
  by_cases hy : y ∈ U
  · rw [show openCollapse U y = (⟨y, hy⟩ : U) from openCollapse_of_mem U ⟨y, hy⟩] at h
    exact congrArg Subtype.val (OnePoint.coe_injective h)
  · rw [openCollapse_of_notMem U hy] at h
    exact False.elim (OnePoint.coe_ne_infty (⟨x, hx⟩ : U) h.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_eq_of_mem ``Submission.DifferentialGeometry.Topology.openCollapse_eq_of_mem

theorem openCollapse_injOn (U : Set Y) : _root_.Set.InjOn (openCollapse U) U :=
  fun _ hx _ _ h => (openCollapse_eq_of_mem hx h.symm).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_injOn ``Submission.DifferentialGeometry.Topology.openCollapse_injOn

def openCollapseOpenPartialHomeomorph [TopologicalSpace Y] [Nonempty Y]
    (U : Set Y) (hU : IsOpen U) : OpenPartialHomeomorph Y (OnePoint U) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((openCollapse_injOn U).toPartialEquiv (openCollapse U) U)
    (by
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun y : U => openCollapse U y)
      have heq : (fun y : U => openCollapse U y) = fun y : U => (y : OnePoint U) :=
        funext (openCollapse_of_mem U)
      rw [heq]
      exact OnePoint.continuous_coe)
    (by
      change IsOpenMap (fun y : U => openCollapse U y)
      have heq : (fun y : U => openCollapse U y) = fun y : U => (y : OnePoint U) :=
        funext (openCollapse_of_mem U)
      rw [heq]
      exact OnePoint.isOpenMap_coe)
    hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph ``Submission.DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph

theorem openCollapseOpenPartialHomeomorph_apply [TopologicalSpace Y] [Nonempty Y]
    (U : Set Y) (hU : IsOpen U) (y : Y) :
    openCollapseOpenPartialHomeomorph U hU y = openCollapse U y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_apply ``Submission.DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_apply

theorem openCollapseOpenPartialHomeomorph_source [TopologicalSpace Y] [Nonempty Y]
    (U : Set Y) (hU : IsOpen U) : (openCollapseOpenPartialHomeomorph U hU).source = U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_source ``Submission.DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_source

theorem openCollapseOpenPartialHomeomorph_target [TopologicalSpace Y] [Nonempty Y]
    (U : Set Y) (hU : IsOpen U) :
    (openCollapseOpenPartialHomeomorph U hU).target = {OnePoint.infty}ᶜ := by
  change openCollapse U '' U = {OnePoint.infty}ᶜ
  rw [OnePoint.compl_infty]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (openCollapse_of_mem U ⟨y, hy⟩).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, y.property, openCollapse_of_mem U y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_target ``Submission.DifferentialGeometry.Topology.openCollapseOpenPartialHomeomorph_target

end DifferentialGeometry.Topology
