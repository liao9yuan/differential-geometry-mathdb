/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Plane
import Mathlib.Topology.UnitInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open _root_.Set _root_.unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ _root_.Set.InjOn f I ∧ f '' I = A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc ``Submission.Schoenflies.IsArc

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ _root_.Set.InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween ``Submission.Schoenflies.IsArcBetween

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : _root_.Set.InjOn f (_root_.Set.Ico 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop ``Submission.Schoenflies.IsLoop

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve ``Submission.Schoenflies.IsJordanCurve

/-! ### The unit interval, as a subset of `ℝ` -/

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.zero_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.zero_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.zero_mem_I ``Submission.Schoenflies.zero_mem_I

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.one_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.one_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.one_mem_I ``Submission.Schoenflies.one_mem_I

theorem isCompact_I : IsCompact I := _root_.CompactIccSpace.isCompact_Icc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isCompact_I then
    throwError "Refusing to shadow existing declaration Schoenflies.isCompact_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isCompact_I ``Submission.Schoenflies.isCompact_I

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isConnected_I then
    throwError "Refusing to shadow existing declaration Schoenflies.isConnected_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isConnected_I ``Submission.Schoenflies.isConnected_I

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous. -/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isCompact_image_of_subset_I then
    throwError "Refusing to shadow existing declaration Schoenflies.isCompact_image_of_subset_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isCompact_image_of_subset_I ``Submission.Schoenflies.isCompact_image_of_subset_I

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween.isArc then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween.isArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween.isArc ``Submission.Schoenflies.IsArcBetween.isArc

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact _root_.Set.mem_image_of_mem f zero_mem_I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween.left_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween.left_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween.left_mem ``Submission.Schoenflies.IsArcBetween.left_mem

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact _root_.Set.mem_image_of_mem f one_mem_I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween.right_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween.right_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween.right_mem ``Submission.Schoenflies.IsArcBetween.right_mem

/-- Running a piece the other way round. -/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween.reverse then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween.reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween.reverse ``Submission.Schoenflies.IsArcBetween.reverse

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc.isCompact then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc.isCompact ``Submission.Schoenflies.IsArc.isCompact

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc.isConnected then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc.isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc.isConnected ``Submission.Schoenflies.IsArc.isConnected

theorem nonempty (h : IsArc A) : A.Nonempty := h.isConnected.nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc.nonempty then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc.nonempty ``Submission.Schoenflies.IsArc.nonempty

theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc.isClosed then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc.isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc.isClosed ``Submission.Schoenflies.IsArc.isClosed

/-- Every arc is an arc between its two endpoints. -/
theorem exists_isArcBetween (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨f, hc, hi, him⟩ := h
  exact ⟨f 0, f 1, f, hc, hi, him, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArc.exists_isArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArc.exists_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArc.exists_isArcBetween ``Submission.Schoenflies.IsArc.exists_isArcBetween

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.isCompact then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.isCompact ``Submission.Schoenflies.IsJordanCurve.isCompact

theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.isConnected then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.isConnected ``Submission.Schoenflies.IsJordanCurve.isConnected

theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.nonempty then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.nonempty ``Submission.Schoenflies.IsJordanCurve.nonempty

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.isClosed then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.isClosed ``Submission.Schoenflies.IsJordanCurve.isClosed

end IsJordanCurve

end Schoenflies
