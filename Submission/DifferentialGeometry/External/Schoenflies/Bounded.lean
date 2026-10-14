/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Square

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Catching a bounded set inside a square

The outer face of a plane graph is found by catching the whole drawing — finitely many points
and finitely many compact arcs — inside one axis-parallel square, and then observing that the
outside of that square is connected (`isConnected_beyondSquare`) and therefore lies in a single
face. This module is the "catching" half.

The key identity is `beyondSquare_eq_compl`: the outside of a square, as defined by a
coordinate inequality, *is* the complement of the closed square. It is what lets the
connectedness theorem be applied to a complement.

## Blueprint

* `beyondSquare_eq_compl` — the outside of a square is the complement of the closed square.
* `exists_closedSquare_of_isBounded`, `IsCompact.exists_closedSquare` — a bounded set is caught
  inside a square about the origin.
* `isOpen_compl_of_finite_isCompact` — the complement of a finite union of compact sets is
  open; the exterior of a plane graph is open for this reason.
-/

open _root_.Metric _root_.Set

namespace Schoenflies

namespace Plane

@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.supDist_zero then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.supDist_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.supDist_zero ``Submission.Schoenflies.Plane.supDist_zero

/-- The outside of a square is exactly the complement of the closed square. -/
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, _root_.Set.mem_ofPred_eq, _root_.Set.mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.beyondSquare_eq_compl then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.beyondSquare_eq_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.beyondSquare_eq_compl ``Submission.Schoenflies.Plane.beyondSquare_eq_compl

/-- A bounded set sits inside a closed square about the origin, of nonnegative radius. -/
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.exists_closedSquare_of_isBounded then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.exists_closedSquare_of_isBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.exists_closedSquare_of_isBounded ``Submission.Schoenflies.Plane.exists_closedSquare_of_isBounded

theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Schoenflies.Plane.IsCompact
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.IsCompact.exists_closedSquare then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.IsCompact.exists_closedSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.IsCompact.exists_closedSquare ``Submission.Schoenflies.Plane.IsCompact.exists_closedSquare

/-- Two squares about the origin merge by taking the larger radius; kept nonnegative so that
callers never split on which is larger. -/
theorem closedSquare_mono {r s : ℝ} (h : r ≤ s) : closedSquare 0 r ⊆ closedSquare 0 s :=
  fun _ hx => le_trans hx h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.closedSquare_mono then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.closedSquare_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.closedSquare_mono ``Submission.Schoenflies.Plane.closedSquare_mono

/-- A finite family of bounded sets is caught inside one square. -/
theorem exists_closedSquare_of_finite {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, Bornology.IsBounded (S i)) :
    ∃ r : ℝ, 0 ≤ r ∧ (⋃ i ∈ t, S i) ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded ((Bornology.isBounded_biUnion ht).2 hS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.exists_closedSquare_of_finite then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.exists_closedSquare_of_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.exists_closedSquare_of_finite ``Submission.Schoenflies.Plane.exists_closedSquare_of_finite

/-- The complement of a finite union of compact sets is open. The exterior of a plane graph —
finitely many vertices and finitely many compact edge arcs — is open for this reason. -/
theorem isOpen_compl_of_finite_isCompact {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, IsCompact (S i)) : IsOpen (⋃ i ∈ t, S i)ᶜ :=
  (ht.isClosed_biUnion fun i hi => (hS i hi).isClosed).isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.isOpen_compl_of_finite_isCompact then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.isOpen_compl_of_finite_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.isOpen_compl_of_finite_isCompact ``Submission.Schoenflies.Plane.isOpen_compl_of_finite_isCompact

end Plane

end Schoenflies
