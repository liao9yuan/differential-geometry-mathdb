import Submission.DifferentialGeometry.Topology.Homotopy.OpenCollapse
import Mathlib.Topology.CompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]


abbrev collapseConstantMaps (U : Set Y) (x : X) :=
  {f : C(Y, X) // ∀ y ∉ U, f y = x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collapseConstantMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collapseConstantMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collapseConstantMaps ``Submission.DifferentialGeometry.Topology.collapseConstantMaps


abbrev basedOnePointMaps (U : Set Y) (x : X) :=
  {f : C(OnePoint U, X) // f OnePoint.infty = x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedOnePointMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedOnePointMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedOnePointMaps ``Submission.DifferentialGeometry.Topology.basedOnePointMaps


def collapseDescendValue (U : Set Y) (x : X) (f : collapseConstantMaps U x) (z : OnePoint U) : X :=
  z.elim x (fun u => f.val u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collapseDescendValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collapseDescendValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collapseDescendValue ``Submission.DifferentialGeometry.Topology.collapseDescendValue



theorem collapseDescendValue_comp (U : Set Y) (x : X) (f : collapseConstantMaps U x) (y : Y) :
    collapseDescendValue U x f (openCollapse U y) = f.val y := by
  classical
  by_cases hy : y ∈ U
  · simp only [openCollapse, dif_pos hy, collapseDescendValue, OnePoint.elim_some]
  · rw [openCollapse_of_notMem U hy]
    exact (f.property y hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collapseDescendValue_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collapseDescendValue_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collapseDescendValue_comp ``Submission.DifferentialGeometry.Topology.collapseDescendValue_comp



theorem continuous_collapseDescendValue [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X) :
    Continuous (fun z : collapseConstantMaps U x × OnePoint U =>
      collapseDescendValue U x z.1 z.2) := by
  apply (openCollapse_prod_quotient U hU hne (collapseConstantMaps U x)).continuous_iff.mpr
  have hc : Continuous (fun z : collapseConstantMaps U x × Y => z.1.val z.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply hc.congr
  intro z
  exact (collapseDescendValue_comp U x z.1 z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_collapseDescendValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_collapseDescendValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_collapseDescendValue ``Submission.DifferentialGeometry.Topology.continuous_collapseDescendValue


def collapseDescend [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X)
    (f : collapseConstantMaps U x) : basedOnePointMaps U x :=
  ⟨⟨collapseDescendValue U x f,
    (continuous_collapseDescendValue U hU hne x).comp (continuous_const.prodMk continuous_id)⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collapseDescend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collapseDescend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collapseDescend ``Submission.DifferentialGeometry.Topology.collapseDescend




def collapseMapsHomeomorph [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X) :
    collapseConstantMaps U x ≃ₜ basedOnePointMaps U x where
  toFun := collapseDescend U hU hne x
  invFun f := ⟨f.val.comp ⟨openCollapse U, continuous_openCollapse U hU⟩,
    fun y hy => by
      change f.val (openCollapse U y) = x
      rw [openCollapse_of_notMem U hy, f.property]⟩
  left_inv f := by
    apply Subtype.ext
    ext y
    exact collapseDescendValue_comp U x f y
  right_inv f := by
    apply Subtype.ext
    ext z
    induction z using OnePoint.rec with
    | infty => exact f.property.symm
    | coe u =>
      change f.val (openCollapse U u) = f.val (u : OnePoint U)
      rw [openCollapse_of_mem]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_collapseDescendValue U hU hne x
  continuous_invFun := ((_root_.ContinuousMap.continuous_precomp
    (⟨openCollapse U, continuous_openCollapse U hU⟩ : C(Y, OnePoint U))).comp
      continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collapseMapsHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collapseMapsHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collapseMapsHomeomorph ``Submission.DifferentialGeometry.Topology.collapseMapsHomeomorph

end DifferentialGeometry.Topology
