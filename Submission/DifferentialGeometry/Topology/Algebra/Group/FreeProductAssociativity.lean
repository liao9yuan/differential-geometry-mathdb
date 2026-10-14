/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.GroupTheory.Coprod.Basic
import Submission.DifferentialGeometry.Topology.Algebra.Group.FreeProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

universe u v

namespace DifferentialGeometry.Algebra.Group


abbrev optionFreeProductFactor {ι : Type u} (G : ι → Type v) (H : Type v) :
    Option ι → Type v
  | none => H
  | some i => G i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.optionFreeProductFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.optionFreeProductFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.optionFreeProductFactor ``Submission.DifferentialGeometry.Algebra.Group.optionFreeProductFactor

instance optionFreeProductFactorGroup {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H]
    (i : Option ι) : Group (optionFreeProductFactor G H i) := by
  cases i <;> simp only [optionFreeProductFactor] <;> infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.optionFreeProductFactorGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.optionFreeProductFactorGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.optionFreeProductFactorGroup ``Submission.DifferentialGeometry.Algebra.Group.optionFreeProductFactorGroup


def coprodIOptionToCoprod {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.CoprodI (optionFreeProductFactor G H) →*
      Monoid.Coprod (Monoid.CoprodI G) H :=
  Monoid.CoprodI.lift fun
    | none => Monoid.Coprod.inr
    | some i => Monoid.Coprod.inl.comp
        (Monoid.CoprodI.of (M := G) (i := i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIOptionToCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIOptionToCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIOptionToCoprod ``Submission.DifferentialGeometry.Algebra.Group.coprodIOptionToCoprod


def coprodToCoprodIOption {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.Coprod (Monoid.CoprodI G) H →*
      Monoid.CoprodI (optionFreeProductFactor G H) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := _root_.Option.some i))
    (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := _root_.Option.none))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodToCoprodIOption then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodToCoprodIOption"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodToCoprodIOption ``Submission.DifferentialGeometry.Algebra.Group.coprodToCoprodIOption

theorem coprodOptionMaps_forward_inverse {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodIOptionToCoprod G H).comp (coprodToCoprodIOption G H) =
      MonoidHom.id (Monoid.Coprod (Monoid.CoprodI G) H) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [coprodIOptionToCoprod, coprodToCoprodIOption]
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodOptionMaps_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodOptionMaps_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodOptionMaps_forward_inverse ``Submission.DifferentialGeometry.Algebra.Group.coprodOptionMaps_forward_inverse

theorem coprodOptionMaps_inverse_forward {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodToCoprodIOption G H).comp (coprodIOptionToCoprod G H) =
      MonoidHom.id (Monoid.CoprodI (optionFreeProductFactor G H)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i with
  | none => rfl
  | some i =>
      ext g
      simp [coprodIOptionToCoprod, coprodToCoprodIOption]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodOptionMaps_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodOptionMaps_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodOptionMaps_inverse_forward ``Submission.DifferentialGeometry.Algebra.Group.coprodOptionMaps_inverse_forward

def coprodIOptionEquivCoprod {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.CoprodI (optionFreeProductFactor G H) ≃*
      Monoid.Coprod (Monoid.CoprodI G) H :=
  MonoidHom.toMulEquiv
    (coprodIOptionToCoprod G H)
    (coprodToCoprodIOption G H)
    (coprodOptionMaps_inverse_forward G H)
    (coprodOptionMaps_forward_inverse G H)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod ``Submission.DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod

theorem coprodIOptionEquivCoprod_comp_none {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodIOptionEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := _root_.Option.none)) =
      Monoid.Coprod.inr := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_none ``Submission.DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_none

theorem coprodIOptionEquivCoprod_comp_some {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H]
    (i : ι) :
    (coprodIOptionEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := _root_.Option.some i)) =
      Monoid.Coprod.inl.comp (Monoid.CoprodI.of (M := G) (i := i)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_some ``Submission.DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod_comp_some

end DifferentialGeometry.Algebra.Group
