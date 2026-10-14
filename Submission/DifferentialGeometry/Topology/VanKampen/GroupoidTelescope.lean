/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Groupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

theorem groupoid_telescope {C : Type u} [Groupoid.{v} C] {n : ℕ}
    {R S : _root_.CategoryTheory.ComposableArrows C n} (α : R ⟶ S) :
    S.hom = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
      ComposableArrows.app' α n (hi := le_rfl) := by
  calc
    S.hom = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≫ S.hom := by
      rw [IsIso.inv_hom_id_assoc]
    _ = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl)) := by
      rw [ComposableArrows.naturality' α 0 n]
    _ = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.groupoid_telescope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.groupoid_telescope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.groupoid_telescope ``Submission.DifferentialGeometry.Topology.VanKampen.groupoid_telescope

section Regression

example {C : Type u} [Groupoid.{v} C] {R S : _root_.CategoryTheory.ComposableArrows C 0} (α : R ⟶ S) :
    S.hom = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := le_rfl)) ≫ R.hom ≫
      ComposableArrows.app' α 0 (hi := le_rfl) :=
  groupoid_telescope α

example {C : Type u} [Groupoid.{v} C] {R S : _root_.CategoryTheory.ComposableArrows C 1} (α : R ⟶ S) :
    S.hom = _root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := by omega)) ≫ R.hom ≫
      ComposableArrows.app' α 1 (hi := le_rfl) :=
  groupoid_telescope α

end Regression

end DifferentialGeometry.Topology.VanKampen
