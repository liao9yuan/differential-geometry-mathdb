/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.PolyPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Polygonal connectedness over a carrier

`Schoenflies.exists_poly_of_isPreconnected` joins two points of an *open* connected subset
of the plane by a polygonal path. The redrawing argument needs the same conclusion for a
carrier that is **not** open in the plane: the ambient set there is the plane minus finitely
many open squares, and the basic neighbourhood of a point on a square's boundary is a
half-disk or a three-quarter disk rather than a ball.

This module restates the clopen argument over an arbitrary carrier `C`. The only hypothesis
on `C` is that it is *locally polygonally connected*: every point has a relatively open
neighbourhood all of whose points it reaches by a polygonal path inside `C`. Openness of `C`
is used nowhere; the ball of the classical proof appears only in
`isLocallyPolyConnected_of_isOpen`, which is what recovers the old statement.

## Blueprint

Brick B6 of `lem:polygonal-redrawing` (H6): polygonal connectivity one level up.

* `PolyReaches` — "joined by a polygonal path inside `C`", as an inductive relation.
  **Note for the integrator:** `Schoenflies/LocallyPolygonal.lean` is being written
  concurrently and defines a relation of the same meaning; the two want unifying.
* `IsLocallyPolyConnected` — the hypothesis replacing openness.
* `PolyReaches.of_isPreconnected` — Lemma 1.1 (polygonal connectedness) over a carrier.
* `exists_poly_of_isPreconnected'` — the old `exists_poly_of_isPreconnected` re-derived from
  it, verbatim; the `example` below it is a machine check that the statements agree.
-/

open _root_.Metric _root_.Set

namespace Schoenflies

variable {C D : Set Plane} {x y z : Plane}

/-! ### Joined by a polygonal path inside a carrier -/

/-- `PolyReaches C x y`: there is a polygonal path from `x` to `y` all of whose segments lie
in `C`. Built at the far end — a path is extended by one segment at a time — because that is
the shape both halves of the clopen argument use. `refl` carries `x ∈ C` so that a constant
path witnesses membership, matching `poly [x] = {x}`. -/
inductive PolyReaches (C : Set Plane) (x : Plane) : Plane → Prop
  | refl (hx : x ∈ C) : PolyReaches C x x
  | step {y z : Plane} (h : PolyReaches C x y) (hseg : segment ℝ y z ⊆ C) : PolyReaches C x z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches ``Submission.Schoenflies.PolyReaches

namespace PolyReaches

/-- A single segment inside `C` is already a polygonal path. -/
theorem of_segment (hseg : segment ℝ x y ⊆ C) : PolyReaches C x y :=
  (PolyReaches.refl (hseg (left_mem_segment ℝ x y))).step hseg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.of_segment then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.of_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.of_segment ``Submission.Schoenflies.PolyReaches.of_segment

theorem left_mem (h : PolyReaches C x y) : x ∈ C := by
  induction h with
  | refl hx => exact hx
  | step _ _ ih => exact ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.left_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.left_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.left_mem ``Submission.Schoenflies.PolyReaches.left_mem

theorem right_mem (h : PolyReaches C x y) : y ∈ C := by
  induction h with
  | refl hx => exact hx
  | @step _ z _ hseg _ => exact hseg (right_mem_segment ℝ _ z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.right_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.right_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.right_mem ``Submission.Schoenflies.PolyReaches.right_mem

theorem trans (h₁ : PolyReaches C x y) (h₂ : PolyReaches C y z) : PolyReaches C x z := by
  induction h₂ with
  | refl _ => exact h₁
  | step _ hseg ih => exact ih.step hseg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.trans then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.trans ``Submission.Schoenflies.PolyReaches.trans

/-- Symmetry: a path is run backwards one segment at a time, each reversed segment being the
same set. -/
theorem symm (h : PolyReaches C x y) : PolyReaches C y x := by
  induction h with
  | refl hx => exact PolyReaches.refl hx
  | @step y z _ hseg ih =>
    -- The last segment, reversed, joins `z` back to `y`; then follow the shorter path back.
    exact (of_segment (by rwa [segment_symm])).trans ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.symm then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.symm ``Submission.Schoenflies.PolyReaches.symm

theorem mono (hCD : C ⊆ D) (h : PolyReaches C x y) : PolyReaches D x y := by
  induction h with
  | refl hx => exact PolyReaches.refl (hCD hx)
  | step _ hseg ih => exact ih.step (hseg.trans hCD)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.mono then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.mono ``Submission.Schoenflies.PolyReaches.mono

end PolyReaches

/-! ### The relation and the vertex-list representation agree -/

/-- A polygonal path in the sense of `PolyReaches` yields a vertex list with the carrier of
its polygon inside `C`. This is `poly_concat` used once per `step`. -/
theorem PolyReaches.exists_poly (h : PolyReaches C x y) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y := by
  induction h with
  | refl hx => exact ⟨[x], by simp, by simpa using hx, rfl, rfl⟩
  | @step _ z _ hseg ih =>
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := ih
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact _root_.Set.union_subset hsub hseg
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.exists_poly then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.exists_poly"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.exists_poly ``Submission.Schoenflies.PolyReaches.exists_poly

/-- Conversely a vertex list whose polygon lies in `C` joins its ends. -/
theorem polyReaches_of_poly_subset : ∀ {vs : List Plane} (hne : vs ≠ []), poly vs ⊆ C →
    PolyReaches C (vs.head hne) (vs.getLast hne)
  | [], hne, _ => absurd rfl hne
  | [v], _, hsub => PolyReaches.refl (hsub (by simp))
  | u :: v :: rest, _, hsub => by
    rw [poly_cons_cons] at hsub
    have hstep : PolyReaches C u v :=
      PolyReaches.of_segment (subset_union_left.trans hsub)
    have hrest := polyReaches_of_poly_subset (List.cons_ne_nil v rest)
      (subset_union_right.trans hsub)
    rw [List.getLast_cons (List.cons_ne_nil v rest)]
    exact hstep.trans hrest

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.polyReaches_of_poly_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.polyReaches_of_poly_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.polyReaches_of_poly_subset ``Submission.Schoenflies.polyReaches_of_poly_subset

/-! ### Local polygonal connectedness -/

/-- `C` is locally polygonally connected when every point of `C` has a relatively open
neighbourhood in `C` each of whose points it reaches by a polygonal path inside `C`.

The neighbourhood is presented as `V ∩ C` for an ambient open `V`, which is exactly what a
relatively open neighbourhood is; the paths are only required to stay inside `C`, not inside
the neighbourhood, since that is all the clopen argument uses and it is the weaker demand on
a producer. Ball, half-disk and three-quarter disk all qualify. -/
def IsLocallyPolyConnected (C : Set Plane) : Prop :=
  ∀ w ∈ C, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ V ∩ C, PolyReaches C w z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLocallyPolyConnected then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLocallyPolyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLocallyPolyConnected ``Submission.Schoenflies.IsLocallyPolyConnected

/-- The relative-openness step, stated once because the clopen argument uses it twice — for
the reachable set and, run backwards, for its relative complement.

A subset of `C` closed under "reach one more point of `C` by a polygonal path" is relatively
open in `C`. The witness is the union of all ambient open sets that are polygonally attached
to a point of `S`; no choice is needed to assemble it. -/
theorem isRelOpen_of_polyReaches_stable (hloc : IsLocallyPolyConnected C) {S : Set Plane}
    (hS : S ⊆ C) (hstable : ∀ w ∈ S, ∀ z ∈ C, PolyReaches C w z → z ∈ S) :
    ∃ U : Set Plane, IsOpen U ∧ S ⊆ U ∧ U ∩ C ⊆ S := by
  refine ⟨⋃₀ {V : Set Plane | IsOpen V ∧ ∃ w ∈ S, ∀ z ∈ V ∩ C, PolyReaches C w z},
    isOpen_sUnion fun V hV => hV.1, fun w hw => ?_, ?_⟩
  · obtain ⟨V, hVopen, hwV, hVreach⟩ := hloc w (hS hw)
    exact ⟨V, ⟨hVopen, w, hw, hVreach⟩, hwV⟩
  · rintro z ⟨⟨V, ⟨_, w, hwS, hVreach⟩, hzV⟩, hzC⟩
    exact hstable w hwS z hzC (hVreach z ⟨hzV, hzC⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isRelOpen_of_polyReaches_stable then
    throwError "Refusing to shadow existing declaration Schoenflies.isRelOpen_of_polyReaches_stable"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isRelOpen_of_polyReaches_stable ``Submission.Schoenflies.isRelOpen_of_polyReaches_stable

/-! ### The theorem -/

/-- Lemma 1.1 (polygonal connectedness) over a carrier: in a relatively connected, locally
polygonally connected set, any two points are joined by a polygonal path inside the set.

The proof is the clopen argument. The points reachable from `x` are relatively open in `C`,
and so are the unreachable ones — the same lemma, since "unreachable" is stable under
reaching too, by symmetry. `IsPreconnected C` then forbids the split. -/
theorem PolyReaches.of_isPreconnected (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : PolyReaches C x y := by
  by_contra hxy
  set R : Set Plane := {w | w ∈ C ∧ PolyReaches C x w} with hRdef
  obtain ⟨U, hUopen, hRU, hUR⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := R) (fun _ hw => hw.1)
      (fun _ hw _ hzC hreach => ⟨hzC, hw.2.trans hreach⟩)
  obtain ⟨U', hU'open, hRU', hU'R⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := C \ R) (fun _ hw => hw.1)
      (fun w hw z hzC hreach => ⟨hzC, fun hzR => hw.2 ⟨hw.1, hzR.2.trans hreach.symm⟩⟩)
  obtain ⟨w, hwC, hwU, hwU'⟩ := hconn U U' hUopen hU'open
    (fun v hv => (em (v ∈ R)).imp (fun h => hRU h) (fun h => hRU' ⟨hv, h⟩))
    ⟨x, hx, hRU ⟨hx, PolyReaches.refl hx⟩⟩
    ⟨y, hy, hRU' ⟨hy, fun h => hxy h.2⟩⟩
  exact (hU'R ⟨hwU', hwC⟩).2 (hUR ⟨hwU, hwC⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PolyReaches.of_isPreconnected then
    throwError "Refusing to shadow existing declaration Schoenflies.PolyReaches.of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PolyReaches.of_isPreconnected ``Submission.Schoenflies.PolyReaches.of_isPreconnected

/-- The vertex-list reading of the carrier theorem, matching the shape `PolyPath` delivers. -/
theorem exists_poly_of_isPreconnected_of_locally (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ C ∧ vs.head h = x ∧ vs.getLast h = y :=
  (PolyReaches.of_isPreconnected hloc hconn hx hy).exists_poly

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.exists_poly_of_isPreconnected_of_locally then
    throwError "Refusing to shadow existing declaration Schoenflies.exists_poly_of_isPreconnected_of_locally"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.exists_poly_of_isPreconnected_of_locally ``Submission.Schoenflies.exists_poly_of_isPreconnected_of_locally

/-! ### Producers of the hypothesis -/

/-- Two convex pieces of `C` that meet make one polygonally connected piece: the bent path
through a common point. This is the shape brick B5 needs for the corner neighbourhood, which
is a disk minus an open quadrant — the union of two half-disks. -/
theorem polyReaches_union_of_convex {S T : Set Plane} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hST : (S ∩ T).Nonempty) (hsub : S ∪ T ⊆ C) (hx : x ∈ S ∪ T) (hy : y ∈ S ∪ T) :
    PolyReaches C x y := by
  obtain ⟨p, hpS, hpT⟩ := hST
  have hSC : ∀ {a b}, a ∈ S → b ∈ S → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hS.segment_subset ha hb).trans (subset_union_left.trans hsub))
  have hTC : ∀ {a b}, a ∈ T → b ∈ T → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hT.segment_subset ha hb).trans (subset_union_right.trans hsub))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hSC hx hy
  · exact (hSC hx hpS).trans (hTC hpT hy)
  · exact (hTC hx hpT).trans (hSC hpS hy)
  · exact hTC hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.polyReaches_union_of_convex then
    throwError "Refusing to shadow existing declaration Schoenflies.polyReaches_union_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.polyReaches_union_of_convex ``Submission.Schoenflies.polyReaches_union_of_convex

/-- An open set is locally polygonally connected: the balls it contains are convex. This is
the only place a ball appears, and it is what recovers the old statement. -/
theorem isLocallyPolyConnected_of_isOpen (hC : IsOpen C) : IsLocallyPolyConnected C := by
  intro w hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hC w hw
  exact ⟨ball w r, _root_.Metric.isOpen_ball, _root_.Metric.mem_ball_self hr, fun z hz =>
    PolyReaches.of_segment
      (((convex_ball w r).segment_subset (_root_.Metric.mem_ball_self hr) hz.1).trans hball)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isLocallyPolyConnected_of_isOpen then
    throwError "Refusing to shadow existing declaration Schoenflies.isLocallyPolyConnected_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isLocallyPolyConnected_of_isOpen ``Submission.Schoenflies.isLocallyPolyConnected_of_isOpen

/-- `PolyPath.exists_poly_of_isPreconnected`, re-derived from the carrier version. -/
theorem exists_poly_of_isPreconnected' {Ω : Set Plane} {x y : Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y :=
  exists_poly_of_isPreconnected_of_locally (isLocallyPolyConnected_of_isOpen hΩ) hconn hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.exists_poly_of_isPreconnected' then
    throwError "Refusing to shadow existing declaration Schoenflies.exists_poly_of_isPreconnected'"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.exists_poly_of_isPreconnected' ``Submission.Schoenflies.exists_poly_of_isPreconnected'

-- The generalisation is genuine: this `rfl` typechecks only if the statement above is
-- literally the one `PolyPath` proves, proof irrelevance doing the rest.
example : @exists_poly_of_isPreconnected = @exists_poly_of_isPreconnected' := rfl

end Schoenflies
