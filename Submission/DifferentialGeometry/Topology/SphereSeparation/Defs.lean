import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open _root_.Set

structure SphereSides {X : Type*} [TopologicalSpace X] (S : Set X) where
  compactSide : Set X
  endSide : Set X
  isOpen_compactSide : IsOpen compactSide
  isOpen_endSide : IsOpen endSide
  isConnected_compactSide : IsConnected compactSide
  isConnected_endSide : IsConnected endSide
  disjoint : Disjoint compactSide endSide
  union_eq_compl : compactSide ∪ endSide = Sᶜ
  isCompact_closure_compactSide : IsCompact (closure compactSide)
  not_isCompact_closure_endSide : ¬ IsCompact (closure endSide)
  frontier_compactSide : frontier compactSide = S
  frontier_endSide : frontier endSide = S
  closure_compactSide : closure compactSide = compactSide ∪ S
  closure_endSide : closure endSide = endSide ∪ S
  interior_closure_compactSide : interior (closure compactSide) = compactSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem compl_eq_union (d : SphereSides S) :
    Sᶜ = d.compactSide ∪ d.endSide :=
  d.union_eq_compl.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compl_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.compl_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compl_eq_union ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.compl_eq_union

theorem compactSide_subset_compl (d : SphereSides S) :
    d.compactSide ⊆ Sᶜ := by
  rw [d.compl_eq_union]
  exact _root_.Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_subset_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_subset_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_subset_compl ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_subset_compl

theorem endSide_subset_compl (d : SphereSides S) :
    d.endSide ⊆ Sᶜ := by
  rw [d.compl_eq_union]
  exact _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_subset_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_subset_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_subset_compl ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_subset_compl

theorem compactSide_disjoint_sphere (d : SphereSides S) :
    Disjoint d.compactSide S := by
  rw [Set.disjoint_left]
  intro x hxB hxS
  exact d.compactSide_subset_compl hxB hxS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_disjoint_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_disjoint_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_disjoint_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_disjoint_sphere

theorem endSide_disjoint_sphere (d : SphereSides S) :
    Disjoint d.endSide S := by
  rw [Set.disjoint_left]
  intro x hxE hxS
  exact d.endSide_subset_compl hxE hxS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_disjoint_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_disjoint_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_disjoint_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_disjoint_sphere

theorem compactSide_nonempty (d : SphereSides S) :
    d.compactSide.Nonempty :=
  d.isConnected_compactSide.nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.compactSide_nonempty

theorem endSide_nonempty (d : SphereSides S) :
    d.endSide.Nonempty :=
  d.isConnected_endSide.nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.endSide_nonempty

theorem subset_compactSide_or_subset_endSide (d : SphereSides S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ) :
    C ⊆ d.compactSide ∨ C ⊆ d.endSide := by
  apply hC.subset_or_subset d.isOpen_compactSide d.isOpen_endSide d.disjoint
  simpa only [d.union_eq_compl] using hCS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_or_subset_endSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_or_subset_endSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_or_subset_endSide ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_or_subset_endSide

theorem subset_compactSide_of_isPreconnected_of_inter_nonempty
    (d : SphereSides S) (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ)
    (hCB : (C ∩ d.compactSide).Nonempty) :
    C ⊆ d.compactSide := by
  exact hC.subset_left_of_subset_union d.isOpen_compactSide d.isOpen_endSide
    d.disjoint (by simpa only [d.union_eq_compl] using hCS) hCB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_of_isPreconnected_of_inter_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_of_isPreconnected_of_inter_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_of_isPreconnected_of_inter_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_compactSide_of_isPreconnected_of_inter_nonempty

theorem subset_endSide_of_isPreconnected_of_inter_nonempty
    (d : SphereSides S) (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ)
    (hCE : (C ∩ d.endSide).Nonempty) :
    C ⊆ d.endSide := by
  exact hC.subset_right_of_subset_union d.isOpen_compactSide d.isOpen_endSide
    d.disjoint (by simpa only [d.union_eq_compl] using hCS) hCE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_endSide_of_isPreconnected_of_inter_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_endSide_of_isPreconnected_of_inter_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_endSide_of_isPreconnected_of_inter_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.subset_endSide_of_isPreconnected_of_inter_nonempty

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
