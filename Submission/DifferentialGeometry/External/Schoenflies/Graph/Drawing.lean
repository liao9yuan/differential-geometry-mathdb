/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Curve
import Submission.DifferentialGeometry.External.Schoenflies.Topology
import Submission.DifferentialGeometry.External.Schoenflies.Bounded
import Submission.DifferentialGeometry.External.Schoenflies.Graph.Degree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open _root_.Metric _root_.Set _root_.Submission.Schoenflies _root_.unitInterval
open scoped _root_.Graph _root_.Submission.Graph

namespace Graph
open _root_.Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

open _root_.Graph in
/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgeArc then
    throwError "Refusing to shadow existing declaration Graph.edgeArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgeArc ``Submission.Graph.edgeArc

open _root_.Graph in
/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ _root_.Set.InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing ``Submission.Graph.IsDrawing

namespace IsDrawing
open _root_.Graph

/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses. -/
theorem edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.edge_isArcBetween then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.edge_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.edge_isArcBetween ``Submission.Graph.IsDrawing.edge_isArcBetween

theorem isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isArc_edgeArc then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isArc_edgeArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isArc_edgeArc ``Submission.Graph.IsDrawing.isArc_edgeArc

theorem isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isCompact_edgeArc then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isCompact_edgeArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isCompact_edgeArc ``Submission.Graph.IsDrawing.isCompact_edgeArc

/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices". -/
theorem arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.arcs_meet_at_vertex then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.arcs_meet_at_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.arcs_meet_at_vertex ``Submission.Graph.IsDrawing.arcs_meet_at_vertex

/-- Away from the vertices, a point of the drawing lies on exactly one edge. This is the form
the polygonal overlay wants. -/
theorem unique_edge_at (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    {p : Plane} (hpV : p ∉ V(G)) (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    e = f := by
  by_contra hef
  exact hpV (h.arcs_meet_at_vertex he hf hef hpe hpf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.unique_edge_at then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.unique_edge_at"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.unique_edge_at ``Submission.Graph.IsDrawing.unique_edge_at

end IsDrawing

/-! ### What a plane graph occupies -/

open _root_.Graph in
/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.pointSet then
    throwError "Refusing to shadow existing declaration Graph.pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.pointSet ``Submission.Graph.pointSet

open _root_.Graph in
theorem vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := _root_.Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.vertexSet_subset_pointSet then
    throwError "Refusing to shadow existing declaration Graph.vertexSet_subset_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.vertexSet_subset_pointSet ``Submission.Graph.vertexSet_subset_pointSet

open _root_.Graph in
theorem edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  _root_.Set.subset_union_of_subset_right (_root_.Set.subset_biUnion_of_mem he) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgeArc_subset_pointSet then
    throwError "Refusing to shadow existing declaration Graph.edgeArc_subset_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgeArc_subset_pointSet ``Submission.Graph.edgeArc_subset_pointSet

/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs. -/
theorem IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isCompact_pointSet then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isCompact_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isCompact_pointSet ``Submission.Graph.IsDrawing.isCompact_pointSet

theorem IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isClosed_pointSet then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isClosed_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isClosed_pointSet ``Submission.Graph.IsDrawing.isClosed_pointSet

open _root_.Graph in
/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.exterior then
    throwError "Refusing to shadow existing declaration Graph.exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.exterior ``Submission.Graph.exterior

theorem IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isOpen_exterior then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isOpen_exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isOpen_exterior ``Submission.Graph.IsDrawing.isOpen_exterior

open _root_.Graph in
/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.face then
    throwError "Refusing to shadow existing declaration Graph.face"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.face ``Submission.Graph.face

open _root_.Graph in
theorem face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.face_subset_exterior then
    throwError "Refusing to shadow existing declaration Graph.face_subset_exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.face_subset_exterior ``Submission.Graph.face_subset_exterior

open _root_.Graph in
theorem mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_face then
    throwError "Refusing to shadow existing declaration Graph.mem_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_face ``Submission.Graph.mem_face

theorem IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.isOpen_face then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.isOpen_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.isOpen_face ``Submission.Graph.IsDrawing.isOpen_face

open _root_.Graph in
theorem isConnected_face (h : base ∈ exterior G drawing) :
    IsConnected (face G drawing base) :=
  ⟨⟨base, mem_face h⟩, isPreconnected_connectedComponentIn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.isConnected_face then
    throwError "Refusing to shadow existing declaration Graph.isConnected_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.isConnected_face ``Submission.Graph.isConnected_face

open _root_.Graph in
/-- Faces partition the exterior: two faces either coincide or are disjoint. -/
theorem face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.face_eq_or_disjoint then
    throwError "Refusing to shadow existing declaration Graph.face_eq_or_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.face_eq_or_disjoint ``Submission.Graph.face_eq_or_disjoint

end Graph
