/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Data.List.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open _root_.Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph
open _root_.Graph

/-! ### The vertices an edge list touches -/

open _root_.Graph in
/-- The vertices lying on at least one edge of `W`. -/
def coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices ``Submission.Graph.coveredVertices

open _root_.Graph in
/-- The vertices a walk from `u` along `W` visits: its source, plus the ends of every edge it
takes. Defined for any edge list, not just for one that walks — the freshness clause of a
path reads it about the *rest* of the path before that rest is known to be a walk at all. -/
def walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := _root_.Insert.insert u (G.coveredVertices W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices then
    throwError "Refusing to shadow existing declaration Graph.walkVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices ``Submission.Graph.walkVertices

open _root_.Graph in
theorem mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_coveredVertices_iff then
    throwError "Refusing to shadow existing declaration Graph.mem_coveredVertices_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_coveredVertices_iff ``Submission.Graph.mem_coveredVertices_iff

open _root_.Graph in
theorem mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_walkVertices_iff then
    throwError "Refusing to shadow existing declaration Graph.mem_walkVertices_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_walkVertices_iff ``Submission.Graph.mem_walkVertices_iff

open _root_.Graph in
@[simp]
theorem coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_nil then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_nil ``Submission.Graph.coveredVertices_nil

open _root_.Graph in
@[simp]
theorem walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices_nil then
    throwError "Refusing to shadow existing declaration Graph.walkVertices_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices_nil ``Submission.Graph.walkVertices_nil

open _root_.Graph in
theorem mem_coveredVertices (he : e ∈ W) (hx : G.Inc e x) : x ∈ G.coveredVertices W :=
  ⟨e, he, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_coveredVertices then
    throwError "Refusing to shadow existing declaration Graph.mem_coveredVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_coveredVertices ``Submission.Graph.mem_coveredVertices

open _root_.Graph in
theorem mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_walkVertices_self then
    throwError "Refusing to shadow existing declaration Graph.mem_walkVertices_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_walkVertices_self ``Submission.Graph.mem_walkVertices_self

open _root_.Graph in
theorem mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_walkVertices_of_mem_covered then
    throwError "Refusing to shadow existing declaration Graph.mem_walkVertices_of_mem_covered"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_walkVertices_of_mem_covered ``Submission.Graph.mem_walkVertices_of_mem_covered

open _root_.Graph in
theorem coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_mono then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_mono ``Submission.Graph.coveredVertices_mono

open _root_.Graph in
theorem walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices_mono then
    throwError "Refusing to shadow existing declaration Graph.walkVertices_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices_mono ``Submission.Graph.walkVertices_mono

open _root_.Graph in
@[simp]
theorem coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_reverse then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_reverse ``Submission.Graph.coveredVertices_reverse

open _root_.Graph in
@[simp]
theorem walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices_reverse then
    throwError "Refusing to shadow existing declaration Graph.walkVertices_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices_reverse ``Submission.Graph.walkVertices_reverse

open _root_.Graph in
theorem coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_append then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_append"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_append ``Submission.Graph.coveredVertices_append

open _root_.Graph in
/-- Every vertex on an edge of the graph is a vertex of the graph. -/
theorem coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_subset_vertexSet then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_subset_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_subset_vertexSet ``Submission.Graph.coveredVertices_subset_vertexSet

open _root_.Graph in
theorem walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices_subset_vertexSet then
    throwError "Refusing to shadow existing declaration Graph.walkVertices_subset_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices_subset_vertexSet ``Submission.Graph.walkVertices_subset_vertexSet

open _root_.Graph in
/-- Moving the visited set across a first step, forwards: a vertex the walk visits is either
the vertex it departs from or a vertex the rest of it visits. This is where the step lemma is
used — the edge `e` has only the two ends `u` and `w`, so a vertex on `e` is one of them. -/
theorem mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_walkVertices_cons then
    throwError "Refusing to shadow existing declaration Graph.mem_walkVertices_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_walkVertices_cons ``Submission.Graph.mem_walkVertices_cons

open _root_.Graph in
/-- Moving the visited set across a first step, backwards. -/
theorem mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_walkVertices_cons_of_mem then
    throwError "Refusing to shadow existing declaration Graph.mem_walkVertices_cons_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_walkVertices_cons_of_mem ``Submission.Graph.mem_walkVertices_cons_of_mem

/-! ### Walks -/

open _root_.Graph in
/-- `G.IsWalk u W v` : the edges of `W`, in order, walk from `u` to `v` in `G`. Each edge is
taken from the vertex the previous one arrived at; the list is read at its head, so the
relation is built at the source end. -/
inductive IsWalk (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a walk. -/
  | nil {x : α} (hx : x ∈ V(G)) : IsWalk (G := G) x [] x
  /-- Taking an edge from the source of a walk prepends it. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : IsWalk (G := G) w W v) :
      IsWalk (G := G) u (e :: W) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk then
    throwError "Refusing to shadow existing declaration Graph.IsWalk"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk ``Submission.Graph.IsWalk

theorem IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.IsWalk
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.single then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.single"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.single ``Submission.Graph.IsWalk.single

theorem IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.left_mem then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.left_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.left_mem ``Submission.Graph.IsWalk.left_mem

theorem IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.right_mem then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.right_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.right_mem ``Submission.Graph.IsWalk.right_mem

/-- The edges of a walk are edges of the graph. -/
theorem IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.edge_mem then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.edge_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.edge_mem ``Submission.Graph.IsWalk.edge_mem

theorem IsWalk.edgeSet_subset (h : G.IsWalk u W v) : ∀ e ∈ W, e ∈ E(G) := fun _ he ↦ h.edge_mem he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.edgeSet_subset then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.edgeSet_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.edgeSet_subset ``Submission.Graph.IsWalk.edgeSet_subset

theorem IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.target_mem_walkVertices then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.target_mem_walkVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.target_mem_walkVertices ``Submission.Graph.IsWalk.target_mem_walkVertices

/-- Every vertex a walk visits is a vertex of the graph — with no hypothesis, since the
empty walk already stands at one. -/
theorem IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.walkVertices_subset then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.walkVertices_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.walkVertices_subset ``Submission.Graph.IsWalk.walkVertices_subset

open _root_.Graph in
@[simp]
theorem isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.isWalk_nil_iff then
    throwError "Refusing to shadow existing declaration Graph.isWalk_nil_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.isWalk_nil_iff ``Submission.Graph.isWalk_nil_iff

theorem IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.eq_of_nil then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.eq_of_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.eq_of_nil ``Submission.Graph.IsWalk.eq_of_nil

/-- The step lemma, run along a whole walk: naming the edges determines the vertices, so a
walk from a given source along a given edge list arrives nowhere else. Its engine is that an
edge has only two ends, `Graph.IsLink.right_unique`, which holds in Mathlib's `Graph` with no
distinctness hypothesis (a loop arrives back where it started, deterministically). -/
theorem IsWalk.target_unique (h : G.IsWalk u W v) (h' : G.IsWalk u W w) : v = w := by
  induction h generalizing w with
  | nil hx => exact h'.eq_of_nil.symm ▸ rfl
  | @cons u w' v e W hl _ ih =>
    cases h' with
    | cons hl' hW' => exact ih (hl.right_unique hl' ▸ hW')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.target_unique then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.target_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.target_unique ``Submission.Graph.IsWalk.target_unique

/-- Walks concatenate, with no side condition. -/
theorem IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.append then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.append"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.append ``Submission.Graph.IsWalk.append

/-- A walk runs backwards along the reverse of its edge list, with no side condition. -/
theorem IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.reverse then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.reverse ``Submission.Graph.IsWalk.reverse

/-- A walk in a subgraph is a walk in the graph. -/
theorem IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.mono then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.mono ``Submission.Graph.IsWalk.mono

/-- A walk of a graph whose edges all survive into a subgraph is a walk of that subgraph.
This is the direction a deletion argument needs: an edge is removed, and a walk that never
used it is still there. -/
theorem IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.anti then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.anti"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.anti ``Submission.Graph.IsWalk.anti

/-- A walk that starts inside a set of vertices and ends outside it crosses the boundary
along one of its own edges. -/
theorem IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.crossing then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.crossing"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.crossing ``Submission.Graph.IsWalk.crossing

/-! ### Paths -/

open _root_.Graph in
/-- `G.IsPath u W v` : a walk from `u` to `v` that never returns to a vertex it has left.
The condition is carried step by step — the vertex a step departs from is not among those the
rest of the path visits — rather than imposed afterwards on a computed vertex list. -/
inductive IsPath (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a path. -/
  | nil {x : α} (hx : x ∈ V(G)) : IsPath (G := G) x [] x
  /-- A step onto a path is allowed when the vertex it departs from is fresh. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : IsPath (G := G) w W v)
      (hfresh : u ∉ G.walkVertices w W) : IsPath (G := G) u (e :: W) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath then
    throwError "Refusing to shadow existing declaration Graph.IsPath"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath ``Submission.Graph.IsPath

theorem IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.IsPath
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.isWalk then
    throwError "Refusing to shadow existing declaration Graph.IsPath.isWalk"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.isWalk ``Submission.Graph.IsPath.isWalk

theorem IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.left_mem then
    throwError "Refusing to shadow existing declaration Graph.IsPath.left_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.left_mem ``Submission.Graph.IsPath.left_mem

theorem IsPath.right_mem (h : G.IsPath u W v) : v ∈ V(G) := h.isWalk.right_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.right_mem then
    throwError "Refusing to shadow existing declaration Graph.IsPath.right_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.right_mem ``Submission.Graph.IsPath.right_mem

theorem IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.edge_mem then
    throwError "Refusing to shadow existing declaration Graph.IsPath.edge_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.edge_mem ``Submission.Graph.IsPath.edge_mem

/-- One edge between two distinct vertices is a path. -/
theorem IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.single then
    throwError "Refusing to shadow existing declaration Graph.IsPath.single"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.single ``Submission.Graph.IsPath.single

/-- A path's step never departs from where it arrives: the freshness clause already says so,
because a walk always visits its own source. -/
theorem IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.cons_ne then
    throwError "Refusing to shadow existing declaration Graph.IsPath.cons_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.cons_ne ``Submission.Graph.IsPath.cons_ne

/-- **A path never takes a loop.** This is why nothing in this file has to assume the graph is
loopless: a step along a loop would depart from the vertex it arrives at, which the freshness
clause forbids. -/
theorem IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      -- `hloop : G.IsLink e x x` shares an edge with `hl : G.IsLink e u w`, so `u = w`.
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.not_isLoopAt then
    throwError "Refusing to shadow existing declaration Graph.IsPath.not_isLoopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.not_isLoopAt ``Submission.Graph.IsPath.not_isLoopAt

/-- A path takes no edge twice: an edge it took again would put the vertex it departed from
back among the ones the rest of the path visits. -/
theorem IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.nodup then
    throwError "Refusing to shadow existing declaration Graph.IsPath.nodup"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.nodup ``Submission.Graph.IsPath.nodup

/-- A path in a subgraph is a path in the graph: the freshness clause reads only which
vertices the remaining edges touch, and a subgraph's edges have the same ends there. -/
theorem IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    -- Freshness travels because `H`'s edges link the same pairs in `G`.
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.mono then
    throwError "Refusing to shadow existing declaration Graph.IsPath.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.mono ``Submission.Graph.IsPath.mono

theorem IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.target_mem_walkVertices then
    throwError "Refusing to shadow existing declaration Graph.IsPath.target_mem_walkVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.target_mem_walkVertices ``Submission.Graph.IsPath.target_mem_walkVertices

/-- A path grows at its **target** end. The relation is built at the source end, so this is
the direction that has to be worked for; it is what reversal runs on. -/
theorem IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    -- The departure vertex is still fresh: the only new edge is `e`, whose ends are the old
    -- target `w` — already visited — and `v`, which the source is not.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.extend_at_target then
    throwError "Refusing to shadow existing declaration Graph.IsPath.extend_at_target"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.extend_at_target ``Submission.Graph.IsPath.extend_at_target

/-- A path runs backwards over the same edges. -/
theorem IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    -- `u` avoids everything the rest of the path visits, and reversal changes none of that.
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.reverse then
    throwError "Refusing to shadow existing declaration Graph.IsPath.reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.reverse ``Submission.Graph.IsPath.reverse

/-- **Cutting a path at a vertex it passes through.** A path through `x` has a piece of itself
running from `x` to its target, and that piece uses only the path's own edges. This is the
engine of `Graph.IsWalk.contains_path`: when the next vertex is already on the path built so
far, the path is cut there instead of extended, so nothing ever gets longer. -/
theorem IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.from_visited then
    throwError "Refusing to shadow existing declaration Graph.IsPath.from_visited"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.from_visited ``Submission.Graph.IsPath.from_visited

/-- A path splits at any vertex it visits, and the far half never returns to the source.
`Graph.IsPath.from_visited` is the suffix alone; the prefix is the awkward half, since the
relation is built at the source end and the prefix is what the induction has to carry
forward. -/
theorem IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    -- The far half's edges are among the rest, which the source already avoided.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.split then
    throwError "Refusing to shadow existing declaration Graph.IsPath.split"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.split ``Submission.Graph.IsPath.split

/-- **Every walk contains a path** between the same two vertices, using only the walk's own
edges. This is the blueprint's "shorten an arbitrary walk at repeated vertices"; the
induction never lengthens anything, because the only alternative to prepending an edge is to
cut the path already built (`Graph.IsPath.from_visited`). -/
theorem IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · -- The step lands on the path already built: cut it there rather than extend it.
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.contains_path then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.contains_path"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.contains_path ``Submission.Graph.IsWalk.contains_path

/-! ### Reachability -/

open _root_.Graph in
/-- `G.Reaches u v` : some walk of `G` runs from `u` to `v`. Stated with a walk rather than a
path because walks are what arguments build — they concatenate and reverse with no side
condition — and a path is recovered on demand (`Graph.Reaches.exists_isPath`). -/
def Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches then
    throwError "Refusing to shadow existing declaration Graph.Reaches"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches ``Submission.Graph.Reaches

theorem Reaches.left_mem (h : G.Reaches u v) : u ∈ V(G) := h.choose_spec.left_mem

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.Reaches
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.left_mem then
    throwError "Refusing to shadow existing declaration Graph.Reaches.left_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.left_mem ``Submission.Graph.Reaches.left_mem

theorem Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.right_mem then
    throwError "Refusing to shadow existing declaration Graph.Reaches.right_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.right_mem ``Submission.Graph.Reaches.right_mem

@[refl]
theorem Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.refl then
    throwError "Refusing to shadow existing declaration Graph.Reaches.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.refl ``Submission.Graph.Reaches.refl

theorem Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.symm then
    throwError "Refusing to shadow existing declaration Graph.Reaches.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.symm ``Submission.Graph.Reaches.symm

theorem Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.trans then
    throwError "Refusing to shadow existing declaration Graph.Reaches.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.trans ``Submission.Graph.Reaches.trans

open _root_.Graph in
theorem reaches_comm : G.Reaches u v ↔ G.Reaches v u := ⟨Reaches.symm, Reaches.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.reaches_comm then
    throwError "Refusing to shadow existing declaration Graph.reaches_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.reaches_comm ``Submission.Graph.reaches_comm

theorem Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.of_isLink then
    throwError "Refusing to shadow existing declaration Graph.Reaches.of_isLink"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.of_isLink ``Submission.Graph.Reaches.of_isLink

theorem Reaches.of_adj (h : G.Adj u v) : G.Reaches u v :=
  let ⟨_, hl⟩ := h; .of_isLink hl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.of_adj then
    throwError "Refusing to shadow existing declaration Graph.Reaches.of_adj"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.of_adj ``Submission.Graph.Reaches.of_adj

/-- Whatever a walk reaches, a path reaches. -/
theorem Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.exists_isPath then
    throwError "Refusing to shadow existing declaration Graph.Reaches.exists_isPath"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.exists_isPath ``Submission.Graph.Reaches.exists_isPath

theorem Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Reaches.mono then
    throwError "Refusing to shadow existing declaration Graph.Reaches.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Reaches.mono ``Submission.Graph.Reaches.mono

/-! ### Connectedness -/

open _root_.Graph in
/-- A graph is connected when it has a vertex and every vertex reaches every other. The
nonemptiness clause is not bureaucracy: it is what makes the counting statements about trees
true as stated. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Connected then
    throwError "Refusing to shadow existing declaration Graph.Connected"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Connected ``Submission.Graph.Connected

theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.Connected
  let env ← Lean.getEnv
  if env.contains `Graph.Connected.nonempty then
    throwError "Refusing to shadow existing declaration Graph.Connected.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Connected.nonempty ``Submission.Graph.Connected.nonempty

theorem Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Connected.reaches then
    throwError "Refusing to shadow existing declaration Graph.Connected.reaches"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Connected.reaches ``Submission.Graph.Connected.reaches

/-- A graph is connected as soon as one vertex reaches all the others: reachability is
symmetric and transitive, so a common hub joins every pair. -/
theorem Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Connected.of_hub then
    throwError "Refusing to shadow existing declaration Graph.Connected.of_hub"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Connected.of_hub ``Submission.Graph.Connected.of_hub

/-- In a connected graph any two vertices are joined by a path — the blueprint's imported
fact about finite graphs, with the finiteness it does not actually need dropped. -/
theorem Connected.exists_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v :=
  (h.reaches hu hv).exists_isPath

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Connected.exists_isPath then
    throwError "Refusing to shadow existing declaration Graph.Connected.exists_isPath"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Connected.exists_isPath ``Submission.Graph.Connected.exists_isPath

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

open _root_.Graph in
theorem coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coveredVertices_mono_of_le then
    throwError "Refusing to shadow existing declaration Graph.coveredVertices_mono_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coveredVertices_mono_of_le ``Submission.Graph.coveredVertices_mono_of_le

open _root_.Graph in
theorem walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.walkVertices_mono_of_le then
    throwError "Refusing to shadow existing declaration Graph.walkVertices_mono_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.walkVertices_mono_of_le ``Submission.Graph.walkVertices_mono_of_le

/-- A path of a graph whose edges all survive into a subgraph is a path of that subgraph —
the companion of `Graph.IsWalk.anti`, which it is otherwise identical to. Freshness comes
down the inclusion because the subgraph's edges touch no vertices the graph's do not. -/
theorem IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsPath.anti then
    throwError "Refusing to shadow existing declaration Graph.IsPath.anti"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsPath.anti ``Submission.Graph.IsPath.anti

open _root_.Graph in
theorem mem_edgeSet_deleteEdges_iff {F : Set β} {f : β} :
    f ∈ E(G.deleteEdges F) ↔ f ∈ E(G) ∧ f ∉ F := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_edgeSet_deleteEdges_iff then
    throwError "Refusing to shadow existing declaration Graph.mem_edgeSet_deleteEdges_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_edgeSet_deleteEdges_iff ``Submission.Graph.mem_edgeSet_deleteEdges_iff

/-- A walk that avoids the deleted names survives the deletion. -/
theorem IsWalk.deleteEdges {F : Set β} (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsWalk u W v :=
  h.anti _root_.Graph.deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.deleteEdges then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.deleteEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.deleteEdges ``Submission.Graph.IsWalk.deleteEdges

end Graph
