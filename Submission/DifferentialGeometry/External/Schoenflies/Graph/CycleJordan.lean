/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Concatenate
import Submission.DifferentialGeometry.External.Schoenflies.Graph.Cycle
import Submission.DifferentialGeometry.External.Schoenflies.Graph.Drawing
import Submission.DifferentialGeometry.External.Schoenflies.Polygonal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open _root_.Set _root_.Submission.Schoenflies _root_.unitInterval
open scoped _root_.Graph _root_.Submission.Graph

namespace Graph
open _root_.Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

open _root_.Graph in
/-- The point set of a list of edges: the union of their edge arcs. A walk is a list of edges,
so this is what a walk of a plane graph draws. -/
def edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgesCover then
    throwError "Refusing to shadow existing declaration Graph.edgesCover"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgesCover ``Submission.Graph.edgesCover

open _root_.Graph in
theorem mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_edgesCover_iff then
    throwError "Refusing to shadow existing declaration Graph.mem_edgesCover_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_edgesCover_iff ``Submission.Graph.mem_edgesCover_iff

open _root_.Graph in
theorem mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_edgesCover then
    throwError "Refusing to shadow existing declaration Graph.mem_edgesCover"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_edgesCover ``Submission.Graph.mem_edgesCover

open _root_.Graph in
@[simp]
theorem edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgesCover_nil then
    throwError "Refusing to shadow existing declaration Graph.edgesCover_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgesCover_nil ``Submission.Graph.edgesCover_nil

open _root_.Graph in
@[simp]
theorem edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgesCover_cons then
    throwError "Refusing to shadow existing declaration Graph.edgesCover_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgesCover_cons ``Submission.Graph.edgesCover_cons

open _root_.Graph in
theorem edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgesCover_mono then
    throwError "Refusing to shadow existing declaration Graph.edgesCover_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgesCover_mono ``Submission.Graph.edgesCover_mono

open _root_.Graph in
/-- A list of edges of the graph occupies part of what the graph occupies. -/
theorem edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgesCover_subset_pointSet then
    throwError "Refusing to shadow existing declaration Graph.edgesCover_subset_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgesCover_subset_pointSet ``Submission.Graph.edgesCover_subset_pointSet

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

/-- **An edge of a plane graph has two distinct ends.** An edge with equal ends would be drawn
by an arc whose parametrisation returns to its start, which its injectivity forbids. -/
theorem IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.ne_of_isLink then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.ne_of_isLink"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.ne_of_isLink ``Submission.Graph.IsDrawing.ne_of_isLink

theorem IsDrawing.not_isLoopAt (h : IsDrawing G drawing) (e : β) (u : Plane) :
    ¬ G.IsLoopAt e u :=
  fun hloop ↦ h.ne_of_isLink hloop rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.not_isLoopAt then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.not_isLoopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.not_isLoopAt ``Submission.Graph.IsDrawing.not_isLoopAt

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-- **The first edge's arc meets the rest of the path only at the waypoint.** Two cases, and
neither is geometric beyond the workhorse `Graph.IsDrawing.arcs_meet_at_vertex`: if the rest
takes the same edge again, the source is one of its ends; if it takes a different one, a
common point is a vertex incident with both, so it is the source or the waypoint. Either way a
point that was the source would put the source among the vertices the rest visits, which is
what the path's freshness clause forbids. -/
theorem IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  -- Taking the same edge again would put the source among the vertices the rest visits.
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.first_edge_meets_rest then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.first_edge_meets_rest"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.first_edge_meets_rest ``Submission.Graph.IsDrawing.first_edge_meets_rest

/-- **The realisation of a path is an arc between its two ends.** The path must go somewhere:
the empty path draws the empty set, which is not an arc.

The induction is on the path, at the source end, and what it carries is the existence of the
arc. At each step the first edge's arc and the rest's arc meet only at the waypoint
(`Graph.IsDrawing.first_edge_meets_rest`), so `Schoenflies.IsArcBetween.concatenate` glues
them. -/
theorem IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · -- A single edge: the rest contributes nothing, and the path arrives where the edge does.
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.path_isArcBetween then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.path_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.path_isArcBetween ``Submission.Graph.IsDrawing.path_isArcBetween

/-! ### The realisation of a cycle -/

/-- The detour of a cycle is a path with at least one edge — an empty detour would return to
where it set out, and the edge it is a detour for has two distinct ends — so it is drawn by an
arc between those ends. -/
theorem IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.detour_isArcBetween then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.detour_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.detour_isArcBetween ``Submission.Graph.IsDrawing.detour_isArcBetween

/-- **The detour of a cycle meets the edge only at the edge's two ends.** A common point lies
on the edge and on some edge of the detour, which the detour does not contain, so it is a
vertex incident with the edge — and an edge has only its two ends. -/
theorem IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.detour_meets_edge then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.detour_meets_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.detour_meets_edge ``Submission.Graph.IsDrawing.detour_meets_edge

/-- **The detour and the edge meet in exactly the edge's two ends.** The inclusion
`Graph.IsDrawing.detour_meets_edge` is what `Schoenflies.IsJordanCurve.of_two_arcs` consumes;
the reverse one is free, since both ends are endpoints of both arcs. -/
theorem IsDrawing.cycle_inter (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    edgesCover drawing D ∩ edgeArc drawing e = {u, v} := by
  have hD := h.detour_isArcBetween hc
  have hE := h.edge_isArcBetween hc.isLink
  refine Set.eq_of_subset_of_subset (fun z hz ↦ h.detour_meets_edge hc hz.1 hz.2) ?_
  rintro z (rfl | rfl)
  exacts [⟨hD.left_mem, hE.left_mem⟩, ⟨hD.right_mem, hE.right_mem⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.cycle_inter then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.cycle_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.cycle_inter ``Submission.Graph.IsDrawing.cycle_inter

/-- **The realisation of a cycle is a Jordan curve.** The detour is drawn by an arc from one
end of the edge to the other, the edge is drawn by an arc back, and the two meet only at those
two ends, so `Schoenflies.IsJordanCurve.of_two_arcs` closes the loop. -/
theorem IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.cycle_isJordanCurve then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.cycle_isJordanCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.cycle_isJordanCurve ``Submission.Graph.IsDrawing.cycle_isJordanCurve

/-- The source of a nonempty walk lies on what the walk draws. -/
theorem IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsWalk.left_mem_edgesCover then
    throwError "Refusing to shadow existing declaration Graph.IsWalk.left_mem_edgesCover"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsWalk.left_mem_edgesCover ``Submission.Graph.IsWalk.left_mem_edgesCover

/-- **A walk of a polygonal plane graph draws a polygonal set.** Consecutive edges share the
vertex between them, so the union stays a single vertex list. -/
theorem IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isPolygonal_edgesCover then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isPolygonal_edgesCover"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isPolygonal_edgesCover ``Submission.Graph.IsDrawing.isPolygonal_edgesCover

end Graph
