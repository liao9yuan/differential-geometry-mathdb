/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.CombinatorialInvariance
import Submission.DifferentialGeometry.External.Schoenflies.GeneralCrosscut
import Submission.DifferentialGeometry.External.Schoenflies.ModelCurve
import Submission.DifferentialGeometry.External.Schoenflies.AccessibleJoin
import Submission.DifferentialGeometry.External.Schoenflies.Jordan
import Submission.DifferentialGeometry.External.Schoenflies.Line

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The initial matched pair

The entry point of Part II (`prop:initial-pair`). `def:generated-structure` builds every later
stage from this one by two elementary operations, so the construction is exported as **data** —
one abstract `CellStructure`, two `Realization`s of it, and the `SkeletonHomeo` between them —
and not as an existentially packaged bundle. `Schoenflies.initial_pair` at the end is only a
restatement of the blueprint sentence; nothing should be consumed through it.

## The shape of the construction

The blueprint's `u : C → S` is taken as *data*, not produced inside the proof, because every
later stage uses the same `u`. `Schoenflies.IsSetHomeoOn` is the set-level form of it, and
`Schoenflies.exists_isSetHomeoOn_modelCurve` produces one from `lem:jordan-circle`.

The **target** side is completely explicit: six marked points on `S` (four corners, `u(a)` on
the top side and `u(b)` on the bottom side), seven straight edges. The **source** side is the
pushforward of the target's outer cycle along `w = u⁻¹`, plus the polygonal crosscut. That
asymmetry is deliberate: nothing about the six source arcs has to be proved, because `w` is
injective on `S` and each drawing condition transfers.

The nonadjacency hypothesis of `prop:initial-pair` is used in exactly one place,
`Schoenflies.openSegment_chord_supNorm_lt`: `u(a)` and `u(b)` lie on **opposite** sides, so
every interior point of the straight chord has sup norm `< 1`, hence lies in `Q°`.

## What is assumed

Exactly two hypotheses are carried, and only by the theorems that need them. Neither is a
restatement of anything proved here.

* `harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ` — `thm:arc-complement`, the standing
  hypothesis of `thm:jordan` in this library. It is what produces `IsSeparating C`, hence the
  Jordan domain the crosscut runs in, and it is threaded into `thm:general-crosscut` in the
  form that theorem takes.
* `hcollars : Schoenflies.HasArcCollars (inside C) d.crossSet` — blueprint Lemma 1.8 (b) for
  the polygonal crosscut, the standing hypothesis of `lem:crosscut-at-most-two`. It is needed
  on the **source** side only: on the target side the chord is a straight segment, so
  `Schoenflies.hasArcCollars_segment` discharges it outright
  (`InitialData.hasArcCollarsTarget`).

## Blueprint

* `Schoenflies.IsSetHomeoOn`, `Schoenflies.exists_isSetHomeoOn_modelCurve` — `lem:jordan-circle`
  in the set-level form the gluing needs.
* `Schoenflies.InitialCell`, `Schoenflies.initSkel`, `Schoenflies.initOuter`,
  `Schoenflies.faceCells`, `Schoenflies.initBoundary`, `Schoenflies.initSub`,
  `Schoenflies.initialStructure` — the base cell structure the blueprint fixes right after
  `def:generated-structure` (tex 1590–1602): six boundary vertices, six outer edges, the
  crosscut edge, two 2-cells, and the stated base value of `≼_abs`.
* `Schoenflies.outerEdgeUniqueFace_initialStructure` — assertion (vi) of
  `lem:cellulation-invariants` for the base structure.
* `Schoenflies.HexData`, `Schoenflies.HexData.realization` — a realization of that record from
  six points and seven parametrizations, with the geometric side conditions isolated;
  `HexData.arcOf`, `HexData.arcOf_false_isArcBetween`, `HexData.arcOf_inter`,
  `HexData.outerSet_realization`, `HexData.nonboundary_eq`,
  `HexData.isConnected_nonboundary` are the `def:admissible-graph` clauses that follow.
* `Schoenflies.isTwoConnected_initSkel`, `Schoenflies.HexData.isTwoConnected_graph` — the
  2-connectivity clause of `def:admissible-graph`, proved once on the abstract graph and
  transported by `lem:combinatorial-invariance` (a).
* `Schoenflies.targetHex`, `Schoenflies.sourceHex` — the two realizations of
  `prop:initial-pair`.
* `Schoenflies.InitialData` — the data of an initial matched pair, with
  `InitialData.sourceRealization`, `InitialData.targetRealization` and
  `InitialData.skeletonHomeo` (the `g` of `def:matched-pair`: `u` on the outer cycle by
  `InitialData.skeletonHomeo_eq_u`, the parameter-matching homeomorphism `P → [u(a), u(b)]` on
  the crosscut by `InitialData.skeletonHomeo_cross`).
* `Schoenflies.InitialData.isCrosscut`, `.isCutPair`, `.source_cells_cover`,
  `.source_cell_isComponent`, `.source_closure_cell_inter` and their target counterparts —
  `thm:general-crosscut` applied on each side: the two abstract 2-cells are realized by the two
  sides of the crosscut, labelled by which arc of the outer cycle their closure meets.
* `Schoenflies.InitialData.exists_initialData`, `Schoenflies.initial_pair` —
  `prop:initial-pair`.
-/

open _root_.Metric _root_.Set _root_.Topology _root_.unitInterval
open scoped _root_.Graph _root_.Submission.Graph

namespace Schoenflies

/-! ### Set-level homeomorphisms

`lem:jordan-circle` is stated in this library with subtype homeomorphisms `↥C ≃ₜ ↥modelCurve`.
Everything below needs `u` as a map of the plane restricted to `C`, because it has to be glued
to a map defined on the crosscut. `IsSetHomeoOn` is that shape, with the inverse supplied as
data — the same convention as `CellStructure.SkeletonHomeo`. -/

/-- `u` maps `X` homeomorphically onto `Y`, with inverse `w`. -/
structure IsSetHomeoOn (u w : Plane → Plane) (X Y : Set Plane) : Prop where
  /-- The map is continuous on its domain. -/
  continuousOn : ContinuousOn u X
  /-- The inverse is continuous on its domain. -/
  continuousOn_inv : ContinuousOn w Y
  /-- The map sends the domain into the codomain. -/
  mapsTo : _root_.Set.MapsTo u X Y
  /-- The inverse sends the codomain into the domain. -/
  mapsTo_inv : _root_.Set.MapsTo w Y X
  /-- The inverse undoes the map. -/
  leftInvOn : _root_.Set.LeftInvOn w u X
  /-- The map undoes the inverse. -/
  rightInvOn : _root_.Set.RightInvOn w u Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn ``Submission.Schoenflies.IsSetHomeoOn

namespace IsSetHomeoOn

variable {u w : Plane → Plane} {X Y : Set Plane}

/-- Running the homeomorphism backwards. -/
theorem symm (h : IsSetHomeoOn u w X Y) : IsSetHomeoOn w u Y X :=
  ⟨h.continuousOn_inv, h.continuousOn, h.mapsTo_inv, h.mapsTo, h.rightInvOn, h.leftInvOn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.symm then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.symm ``Submission.Schoenflies.IsSetHomeoOn.symm

theorem injOn (h : IsSetHomeoOn u w X Y) : _root_.Set.InjOn u X := h.leftInvOn.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.injOn then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.injOn ``Submission.Schoenflies.IsSetHomeoOn.injOn

theorem injOn_inv (h : IsSetHomeoOn u w X Y) : _root_.Set.InjOn w Y := h.rightInvOn.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.injOn_inv then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.injOn_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.injOn_inv ``Submission.Schoenflies.IsSetHomeoOn.injOn_inv

theorem image_eq (h : IsSetHomeoOn u w X Y) : u '' X = Y :=
  Subset.antisymm (image_subset_iff.2 h.mapsTo) fun y hy =>
    ⟨w y, h.mapsTo_inv hy, h.rightInvOn hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.image_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.image_eq ``Submission.Schoenflies.IsSetHomeoOn.image_eq

theorem image_inv_eq (h : IsSetHomeoOn u w X Y) : w '' Y = X := h.symm.image_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.image_inv_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.image_inv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.image_inv_eq ``Submission.Schoenflies.IsSetHomeoOn.image_inv_eq

/-- The image of a relatively open subset of the domain is relatively open in the codomain.
This is what makes the two open arcs of `prop:initial-pair` relatively open in `C`, hence able
to meet the countable dense set of strongly accessible points. -/
theorem image_isRelOpen (h : IsSetHomeoOn u w X Y) {U V : Set Plane} (hV : IsOpen V)
    (hU : U = V ∩ X) : ∃ W : Set Plane, IsOpen W ∧ u '' U = W ∩ Y := by
  obtain ⟨W, hWopen, hW⟩ := (_root_.continuousOn_iff'.1 h.continuousOn_inv) V hV
  refine ⟨W, hWopen, ?_⟩
  rw [hU, ← hW]
  ext y
  constructor
  · rintro ⟨x, ⟨hxV, hxX⟩, rfl⟩
    exact ⟨by rwa [_root_.Set.mem_preimage, h.leftInvOn hxX], h.mapsTo hxX⟩
  · rintro ⟨hyw, hyY⟩
    exact ⟨w y, ⟨hyw, h.mapsTo_inv hyY⟩, h.rightInvOn hyY⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsSetHomeoOn.image_isRelOpen then
    throwError "Refusing to shadow existing declaration Schoenflies.IsSetHomeoOn.image_isRelOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsSetHomeoOn.image_isRelOpen ``Submission.Schoenflies.IsSetHomeoOn.image_isRelOpen

end IsSetHomeoOn

/-- **`lem:jordan-circle`, in set-level form.** A Jordan curve carries a homeomorphism onto the
model curve, presented as a pair of maps of the plane. -/
theorem exists_isSetHomeoOn_modelCurve {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ u w : Plane → Plane, IsSetHomeoOn u w C modelCurve := by
  classical
  obtain ⟨h⟩ := hC.homeomorph_modelCurve
  refine ⟨fun p => if hp : p ∈ C then (h ⟨p, hp⟩ : Plane) else 0,
    fun q => if hq : q ∈ modelCurve then (h.symm ⟨q, hq⟩ : Plane) else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (C.domRestrict fun p => if hp : p ∈ C then (h ⟨p, hp⟩ : Plane) else 0) =
        fun p : ↥C => (h p : Plane) := by
      funext p; simp [Set.domRestrict, p.2]
    rw [this]
    exact continuous_subtype_val.comp h.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (modelCurve.domRestrict fun q => if hq : q ∈ modelCurve then (h.symm ⟨q, hq⟩ : Plane)
        else 0) = fun q : ↥modelCurve => (h.symm q : Plane) := by
      funext q; simp [Set.domRestrict, q.2]
    rw [this]
    exact continuous_subtype_val.comp h.symm.continuous
  · intro p hp; simp only [dif_pos hp]; exact (h ⟨p, hp⟩).2
  · intro q hq; simp only [dif_pos hq]; exact (h.symm ⟨q, hq⟩).2
  · intro p hp
    have hmem : (h ⟨p, hp⟩ : Plane) ∈ modelCurve := (h ⟨p, hp⟩).2
    simp only [dif_pos hp, dif_pos hmem]
    have : (⟨(h ⟨p, hp⟩ : Plane), hmem⟩ : ↥modelCurve) = h ⟨p, hp⟩ := rfl
    rw [this, h.symm_apply_apply]
  · intro q hq
    have hmem : (h.symm ⟨q, hq⟩ : Plane) ∈ C := (h.symm ⟨q, hq⟩).2
    simp only [dif_pos hq, dif_pos hmem]
    have : (⟨(h.symm ⟨q, hq⟩ : Plane), hmem⟩ : ↥C) = h.symm ⟨q, hq⟩ := rfl
    rw [this, h.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.exists_isSetHomeoOn_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.exists_isSetHomeoOn_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.exists_isSetHomeoOn_modelCurve ``Submission.Schoenflies.exists_isSetHomeoOn_modelCurve

/-! ### The fifteen cells of the initial structure

The blueprint fixes the base value of `≼_abs` immediately after `def:generated-structure`
(tex 1590–1602). Its cells are the six boundary vertices — the four corner preimages together
with `a, b` —, the six open outer edges into which they divide `C`, the crosscut edge `P`, and
the two 2-cells `R₁, R₂`.

The six vertices are indexed **cyclically** by `Fin 6`, in the order they occur along `C`:

    vert 0 = u⁻¹(1,1)   vert 1 = a   vert 2 = u⁻¹(-1,1)
    vert 3 = u⁻¹(-1,-1) vert 4 = b   vert 5 = u⁻¹(1,-1)

so that `a` lies in the corner arc between corners `0` and `1` and `b` in the corner arc
between corners `2` and `3` — the nonadjacency of `prop:initial-pair`, here visible as
`vert 1` and `vert 4` being antipodal in `Fin 6`. `edge i` runs from `vert i` to `vert (i+1)`,
and `chord` from `vert 1` to `vert 4`.

The two boundary edge-paths from `a` to `b` are therefore `B₁ = [edge 1, edge 2, edge 3]`
(through the corners `2, 3`) and `B₂ = [edge 4, edge 5, edge 0]` (through the corners `5, 0`);
both contain corner vertices, as the blueprint observes. `face false` is `R₁` and `face true`
is `R₂`. -/

/-- A cell of the initial matched cell structure. -/
inductive InitialCell
  /-- One of the six boundary vertices, in cyclic order along `C`. -/
  | vert : Fin 6 → InitialCell
  /-- The outer edge from `vert i` to `vert (i + 1)`. -/
  | edge : Fin 6 → InitialCell
  /-- The crosscut edge, from `vert 1` to `vert 4`. -/
  | chord : InitialCell
  /-- One of the two 2-cells: `face false` is `R₁`, `face true` is `R₂`. -/
  | face : Bool → InitialCell
  /-- A spare name, belonging to no cell of the initial structure.

  The initial structure uses fifteen names; this constructor adds countably many more that it
  never uses. It is here for one reason: `thm:finite-transfer` needs `[Infinite γ]`, because an
  ear insertion consumes fresh cell names and on a finite name type the step is false. Without a
  spare supply the base case could not feed the recursion at all. Nothing below ever produces an
  `aux`, and no cell of `initialStructure` is one. -/
  | aux : ℕ → InitialCell
  deriving DecidableEq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell ``Submission.Schoenflies.InitialCell

namespace InitialCell

/-- The two ends of a cell, when it is an edge. Junk elsewhere; the graph below only ever
consults it on an edge name. -/
def ends : InitialCell → InitialCell × InitialCell
  | .edge i => (.vert i, .vert (i + 1))
  | .chord => (.vert 1, .vert 4)
  | c => (c, c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.ends then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.ends"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.ends ``Submission.Schoenflies.InitialCell.ends

/-- The six 0-cells. -/
def vertices : Set InitialCell := Set.range InitialCell.vert

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.vertices then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.vertices ``Submission.Schoenflies.InitialCell.vertices

/-- The seven 1-cells: six outer edges and the crosscut. -/
def edges : Set InitialCell := Set.range InitialCell.edge ∪ {InitialCell.chord}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.edges ``Submission.Schoenflies.InitialCell.edges

/-- The six outer 1-cells. -/
def outerEdges : Set InitialCell := Set.range InitialCell.edge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.outerEdges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.outerEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.outerEdges ``Submission.Schoenflies.InitialCell.outerEdges

/-- The two 2-cells. -/
def faces : Set InitialCell := Set.range InitialCell.face

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.faces then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.faces"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.faces ``Submission.Schoenflies.InitialCell.faces

theorem outerEdges_subset_edges : outerEdges ⊆ edges := Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.outerEdges_subset_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.outerEdges_subset_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.outerEdges_subset_edges ``Submission.Schoenflies.InitialCell.outerEdges_subset_edges

theorem edge_mem_edges (i : Fin 6) : InitialCell.edge i ∈ edges := Or.inl ⟨i, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.edge_mem_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.edge_mem_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.edge_mem_edges ``Submission.Schoenflies.InitialCell.edge_mem_edges

theorem chord_mem_edges : InitialCell.chord ∈ edges := Or.inr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.chord_mem_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.chord_mem_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.chord_mem_edges ``Submission.Schoenflies.InitialCell.chord_mem_edges

theorem vert_mem_vertices (i : Fin 6) : InitialCell.vert i ∈ vertices := ⟨i, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.vert_mem_vertices then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.vert_mem_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.vert_mem_vertices ``Submission.Schoenflies.InitialCell.vert_mem_vertices

/-- Both ends of a 1-cell are 0-cells. -/
theorem ends_mem_vertices {e : InitialCell} (he : e ∈ edges) :
    e.ends.1 ∈ vertices ∧ e.ends.2 ∈ vertices := by
  rcases he with ⟨i, rfl⟩ | rfl
  · exact ⟨⟨i, rfl⟩, ⟨i + 1, rfl⟩⟩
  · exact ⟨⟨1, rfl⟩, ⟨4, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.ends_mem_vertices then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.ends_mem_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.ends_mem_vertices ``Submission.Schoenflies.InitialCell.ends_mem_vertices

theorem finite_vertices : vertices.Finite := Set.finite_range _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.finite_vertices then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.finite_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.finite_vertices ``Submission.Schoenflies.InitialCell.finite_vertices

theorem finite_edges : edges.Finite := (Set.finite_range _).union (Set.finite_singleton _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.finite_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.finite_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.finite_edges ``Submission.Schoenflies.InitialCell.finite_edges

theorem finite_faces : faces.Finite := Set.finite_range _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.finite_faces then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.finite_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.finite_faces ``Submission.Schoenflies.InitialCell.finite_faces

theorem disjoint_vertices_edges : Disjoint vertices edges := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ (⟨j, hj⟩ | hj) <;> exact absurd hj (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.disjoint_vertices_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.disjoint_vertices_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.disjoint_vertices_edges ``Submission.Schoenflies.InitialCell.disjoint_vertices_edges

theorem disjoint_faces_vertices : Disjoint faces vertices := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ ⟨j, hj⟩
  exact absurd hj (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.disjoint_faces_vertices then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.disjoint_faces_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.disjoint_faces_vertices ``Submission.Schoenflies.InitialCell.disjoint_faces_vertices

theorem disjoint_faces_edges : Disjoint faces edges := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ (⟨j, hj⟩ | hj) <;> exact absurd hj (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialCell.disjoint_faces_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialCell.disjoint_faces_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialCell.disjoint_faces_edges ``Submission.Schoenflies.InitialCell.disjoint_faces_edges

end InitialCell

/-- The abstract 1-skeleton of the initial structure: a hexagon with one long chord. -/
def initSkel : Graph InitialCell InitialCell where
  vertexSet := InitialCell.vertices
  edgeSet := InitialCell.edges
  IsLink e x y := e ∈ InitialCell.edges ∧
    ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by
    rintro e x y ⟨he, hxy | hxy⟩
    exacts [hxy.1 ▸ (InitialCell.ends_mem_vertices he).1,
      hxy.1 ▸ (InitialCell.ends_mem_vertices he).2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSkel ``Submission.Schoenflies.initSkel

/-- The distinguished outer cycle: the same hexagon without the chord. -/
def initOuter : Graph InitialCell InitialCell where
  vertexSet := InitialCell.vertices
  edgeSet := InitialCell.outerEdges
  IsLink e x y := e ∈ InitialCell.outerEdges ∧
    ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by
    rintro e x y ⟨he, hxy | hxy⟩
    exacts [hxy.1 ▸ (InitialCell.ends_mem_vertices (InitialCell.outerEdges_subset_edges he)).1,
      hxy.1 ▸ (InitialCell.ends_mem_vertices (InitialCell.outerEdges_subset_edges he)).2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initOuter then
    throwError "Refusing to shadow existing declaration Schoenflies.initOuter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initOuter ``Submission.Schoenflies.initOuter

@[simp] theorem vertexSet_initSkel : V(initSkel) = InitialCell.vertices := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.vertexSet_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.vertexSet_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.vertexSet_initSkel ``Submission.Schoenflies.vertexSet_initSkel

@[simp] theorem edgeSet_initSkel : E(initSkel) = InitialCell.edges := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.edgeSet_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.edgeSet_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.edgeSet_initSkel ``Submission.Schoenflies.edgeSet_initSkel

@[simp] theorem vertexSet_initOuter : V(initOuter) = InitialCell.vertices := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.vertexSet_initOuter then
    throwError "Refusing to shadow existing declaration Schoenflies.vertexSet_initOuter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.vertexSet_initOuter ``Submission.Schoenflies.vertexSet_initOuter

@[simp] theorem edgeSet_initOuter : E(initOuter) = InitialCell.outerEdges := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.edgeSet_initOuter then
    throwError "Refusing to shadow existing declaration Schoenflies.edgeSet_initOuter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.edgeSet_initOuter ``Submission.Schoenflies.edgeSet_initOuter

theorem initSkel_isLink {e x y : InitialCell} :
    initSkel.IsLink e x y ↔ e ∈ InitialCell.edges ∧
      ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1)) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSkel_isLink then
    throwError "Refusing to shadow existing declaration Schoenflies.initSkel_isLink"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSkel_isLink ``Submission.Schoenflies.initSkel_isLink

theorem initSkel_isLink_ends {e : InitialCell} (he : e ∈ InitialCell.edges) :
    initSkel.IsLink e e.ends.1 e.ends.2 := ⟨he, Or.inl ⟨rfl, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSkel_isLink_ends then
    throwError "Refusing to shadow existing declaration Schoenflies.initSkel_isLink_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSkel_isLink_ends ``Submission.Schoenflies.initSkel_isLink_ends

theorem initOuter_le_initSkel : initOuter ≤ initSkel :=
  ⟨subset_rfl, fun _ _ _ h => ⟨InitialCell.outerEdges_subset_edges h.1, h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initOuter_le_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.initOuter_le_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initOuter_le_initSkel ``Submission.Schoenflies.initOuter_le_initSkel

/-- The cells lying on the closed boundary of a 2-cell: the vertices and edges of `Bᵢ`
together with the crosscut. `face false = R₁` is bounded by `B₁ ∪ P`, `face true = R₂` by
`B₂ ∪ P`. -/
def faceCells : Bool → Set InitialCell
  | false => {.vert 1, .vert 2, .vert 3, .vert 4, .edge 1, .edge 2, .edge 3, .chord}
  | true => {.vert 4, .vert 5, .vert 0, .vert 1, .edge 4, .edge 5, .edge 0, .chord}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.faceCells then
    throwError "Refusing to shadow existing declaration Schoenflies.faceCells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.faceCells ``Submission.Schoenflies.faceCells

/-- The cyclic boundary walk of each 2-cell, as a list of edge names. -/
def initBoundary : InitialCell → List InitialCell
  | .face _root_.Bool.false => [.edge 1, .edge 2, .edge 3, .chord]
  | .face _root_.Bool.true => [.edge 4, .edge 5, .edge 0, .chord]
  | _ => []

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initBoundary then
    throwError "Refusing to shadow existing declaration Schoenflies.initBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initBoundary ``Submission.Schoenflies.initBoundary

/-- The names that `initialStructure` declares to be cells: the six 0-cells, the seven 1-cells
and the two 2-cells. This is `initialStructure.cells` unfolded, written out here because
`initSub` is a field of `initialStructure` and cannot refer to it. -/
def cellNames : Set InitialCell :=
  InitialCell.vertices ∪ InitialCell.edges ∪ InitialCell.faces

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cellNames then
    throwError "Refusing to shadow existing declaration Schoenflies.cellNames"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cellNames ``Submission.Schoenflies.cellNames

theorem aux_notMem_cellNames (n : ℕ) : InitialCell.aux n ∉ cellNames := by
  rintro ((⟨i, hi⟩ | ⟨i, hi⟩ | hi) | ⟨k, hk⟩)
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.aux_notMem_cellNames then
    throwError "Refusing to shadow existing declaration Schoenflies.aux_notMem_cellNames"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.aux_notMem_cellNames ``Submission.Schoenflies.aux_notMem_cellNames

/-- **The base value of `≼_abs`** (tex 1590–1602): the reflexive pairs, the incidence of each
vertex with the edges it bounds, and, for `i = 1, 2`, the incidence of every vertex and edge of
`Bᵢ ∪ P` with `Rᵢ`. Nothing else.

The reflexive clause is restricted to `cellNames`. `≼_abs` must relate cells to cells —
`CellStructure.CombInvariants.sub_mem_left` and `.sub_mem_right` say so — and `InitialCell`
carries a spare supply of names beyond the fifteen cells, so unrestricted reflexivity would
relate a spare name to itself and make both false. -/
def initSub (c d : InitialCell) : Prop :=
  (c = d ∧ d ∈ cellNames) ∨ (d ∈ InitialCell.edges ∧ (c = d.ends.1 ∨ c = d.ends.2)) ∨
    (∃ k, d = .face k ∧ c ∈ faceCells k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSub then
    throwError "Refusing to shadow existing declaration Schoenflies.initSub"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSub ``Submission.Schoenflies.initSub

theorem initSub_refl {c : InitialCell} (hc : c ∈ cellNames) : initSub c c := Or.inl ⟨rfl, hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSub_refl then
    throwError "Refusing to shadow existing declaration Schoenflies.initSub_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSub_refl ``Submission.Schoenflies.initSub_refl

theorem initSub_ends {e : InitialCell} (he : e ∈ InitialCell.edges) :
    initSub e.ends.1 e ∧ initSub e.ends.2 e :=
  ⟨Or.inr (Or.inl ⟨he, Or.inl rfl⟩), Or.inr (Or.inl ⟨he, Or.inr rfl⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSub_ends then
    throwError "Refusing to shadow existing declaration Schoenflies.initSub_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSub_ends ``Submission.Schoenflies.initSub_ends

theorem initSub_face {k : Bool} {c : InitialCell} (h : c ∈ faceCells k) :
    initSub c (.face k) := Or.inr (Or.inr ⟨k, rfl, h⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initSub_face then
    throwError "Refusing to shadow existing declaration Schoenflies.initSub_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initSub_face ``Submission.Schoenflies.initSub_face

/-- **The abstract record of the initial matched cellulation.** -/
def initialStructure : CellStructure InitialCell where
  skel := initSkel
  faces := InitialCell.faces
  outerGraph := initOuter
  outerGraph_le := initOuter_le_initSkel
  boundary := initBoundary
  sub := initSub
  finite_vertexSet := InitialCell.finite_vertices
  finite_edgeSet := InitialCell.finite_edges
  finite_faces := InitialCell.finite_faces
  disjoint_vertexSet_edgeSet := InitialCell.disjoint_vertices_edges
  disjoint_faces_vertexSet := InitialCell.disjoint_faces_vertices
  disjoint_faces_edgeSet := InitialCell.disjoint_faces_edges

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initialStructure then
    throwError "Refusing to shadow existing declaration Schoenflies.initialStructure"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initialStructure ``Submission.Schoenflies.initialStructure

@[simp] theorem initialStructure_skel : initialStructure.skel = initSkel := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initialStructure_skel then
    throwError "Refusing to shadow existing declaration Schoenflies.initialStructure_skel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initialStructure_skel ``Submission.Schoenflies.initialStructure_skel

@[simp] theorem initialStructure_sub : initialStructure.sub = initSub := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initialStructure_sub then
    throwError "Refusing to shadow existing declaration Schoenflies.initialStructure_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initialStructure_sub ``Submission.Schoenflies.initialStructure_sub

@[simp] theorem initialStructure_faces : initialStructure.faces = InitialCell.faces := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initialStructure_faces then
    throwError "Refusing to shadow existing declaration Schoenflies.initialStructure_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initialStructure_faces ``Submission.Schoenflies.initialStructure_faces

@[simp] theorem initialStructure_outerGraph : initialStructure.outerGraph = initOuter := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initialStructure_outerGraph then
    throwError "Refusing to shadow existing declaration Schoenflies.initialStructure_outerGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initialStructure_outerGraph ``Submission.Schoenflies.initialStructure_outerGraph

/-- **Every outer edge is a subcell of exactly one 2-cell** — assertion (vi) of
`lem:cellulation-invariants` for the base structure, and the hypothesis of
`CellStructure.outerEdge_face_corresponds`. The edges of `B₁` bound `R₁` only and those of
`B₂` bound `R₂` only, which is the whole content. -/
theorem outerEdgeUniqueFace_initialStructure :
    CellStructure.OuterEdgeUniqueFace initialStructure := by
  rintro e ⟨i, rfl⟩
  -- an outer edge is a subcell of a 2-cell exactly when it is listed among its cells
  have hsub : ∀ k : Bool, initSub (InitialCell.edge i) (InitialCell.face k) ↔
      InitialCell.edge i ∈ faceCells k := by
    intro k
    refine ⟨?_, fun h => initSub_face h⟩
    rintro (h | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact hmem
  refine ⟨.face (![_root_.Bool.true, _root_.Bool.false, _root_.Bool.false, _root_.Bool.false, _root_.Bool.true, _root_.Bool.true] i), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [initialStructure_sub, hsub]
    fin_cases i <;> simp [faceCells]
  · rintro T ⟨⟨k, rfl⟩, hT⟩
    rw [initialStructure_sub, hsub] at hT
    have : k = ![_root_.Bool.true, _root_.Bool.false, _root_.Bool.false, _root_.Bool.false, _root_.Bool.true, _root_.Bool.true] i := by
      fin_cases i <;> cases k <;> simp_all [faceCells]
    rw [this]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.outerEdgeUniqueFace_initialStructure then
    throwError "Refusing to shadow existing declaration Schoenflies.outerEdgeUniqueFace_initialStructure"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.outerEdgeUniqueFace_initialStructure ``Submission.Schoenflies.outerEdgeUniqueFace_initialStructure

/-! ### A realization of the initial structure, from six points and seven parametrizations

Both realizations of `prop:initial-pair` have the same shape: six points in cyclic position,
six parametrized arcs joining consecutive ones, and one chord from the second point to the
fifth. `HexData` bundles that shape together with the three geometric side conditions a plane
drawing needs, and `HexData.realization` turns it into a `CellStructure.Realization` of
`initialStructure`. Building it once means the square side and the curve side are checked
against the same list.

The pairwise-meeting conditions are stated in the weakest usable form: two outer arcs meet
only in points that are ends of both, and the chord meets each outer arc only in its own two
ends. Everything `IsDrawing` asks for follows, including "an arc contains no vertex but its
own two ends", which is *derived* rather than assumed (`HexData.mem_outer_iff`). -/

/-- The geometric data of one realization of `initialStructure`. -/
structure HexData where
  /-- Where the six boundary vertices sit, in cyclic order. -/
  pos : Fin 6 → Plane
  /-- The parametrization of the outer edge from `pos i` to `pos (i + 1)`. -/
  outer : Fin 6 → ℝ → Plane
  /-- The parametrization of the crosscut, from `pos 1` to `pos 4`. -/
  chordParam : ℝ → Plane
  /-- The six vertices are distinct. -/
  injective_pos : Function.Injective pos
  /-- Each outer edge is drawn continuously. -/
  continuousOn_outer : ∀ i, ContinuousOn (outer i) I
  /-- Each outer edge is drawn injectively. -/
  injOn_outer : ∀ i, _root_.Set.InjOn (outer i) I
  /-- An outer edge starts at its first vertex. -/
  outer_zero : ∀ i, outer i 0 = pos i
  /-- An outer edge ends at the next vertex. -/
  outer_one : ∀ i, outer i 1 = pos (i + 1)
  /-- The crosscut is drawn continuously. -/
  continuousOn_chord : ContinuousOn chordParam I
  /-- The crosscut is drawn injectively. -/
  injOn_chord : _root_.Set.InjOn chordParam I
  /-- The crosscut starts at `a`. -/
  chord_zero : chordParam 0 = pos 1
  /-- The crosscut ends at `b`. -/
  chord_one : chordParam 1 = pos 4
  /-- Two distinct outer edges meet only at points that are ends of both. -/
  outer_meet : ∀ i j, i ≠ j → outer i '' I ∩ outer j '' I ⊆
    ({pos i, pos (i + 1)} : Set Plane) ∩ {pos j, pos (j + 1)}
  /-- The crosscut meets each outer edge only at its own two ends. -/
  chord_meet : ∀ i, chordParam '' I ∩ outer i '' I ⊆ ({pos 1, pos 4} : Set Plane)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData ``Submission.Schoenflies.HexData

namespace HexData

variable (H : HexData)

/-- Where each 0-cell sits. Junk on the other cells, which `Realization` never reads. -/
def point : InitialCell → Plane
  | .vert i => H.pos i
  | _ => 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.point then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.point"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.point ``Submission.Schoenflies.HexData.point

/-- How each 1-cell is drawn. Junk on the other cells. -/
def draw : InitialCell → ℝ → Plane
  | .edge i => H.outer i
  | .chord => H.chordParam
  | _ => fun _ => 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.draw then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.draw"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.draw ``Submission.Schoenflies.HexData.draw

/-- The crosscut, as a set. -/
def chordSet : Set Plane := H.chordParam '' I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.chordSet then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.chordSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.chordSet ``Submission.Schoenflies.HexData.chordSet

/-- The two boundary edge-paths from `pos 1` to `pos 4`, as sets: `arcOf false` is `A₁`, the
union of the outer edges `1, 2, 3`, and `arcOf true` is `A₂`, the union of `4, 5, 0`. -/
def arcOf : Bool → Set Plane
  | false => H.outer 1 '' I ∪ (H.outer 2 '' I ∪ H.outer 3 '' I)
  | true => H.outer 4 '' I ∪ (H.outer 5 '' I ∪ H.outer 0 '' I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.arcOf then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.arcOf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.arcOf ``Submission.Schoenflies.HexData.arcOf

/-- The realized outer cycle, as the union of the six outer edges. -/
def outerArcs : Set Plane := ⋃ i : Fin 6, H.outer i '' I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.outerArcs ``Submission.Schoenflies.HexData.outerArcs

/-- The point set of each open cell.

The 2-cell `face k` is realized by the *side* of the crosscut belonging to `Aₖ`, exactly as the
blueprint prescribes (tex 1590–1602): "the 2-cell `Rᵢ` is realized in the source as the crosscut
side whose closure meets `C` in `Aᵢ`". By `thm:general-crosscut` that side is
`Int(Aᵢ ∪ P)` = `inside (arcOf k ∪ chordSet)`, and taking this as the *definition* makes the
crosscut theorem apply to it with nothing to transport. -/
def cellSet : InitialCell → Set Plane
  | .vert i => {H.pos i}
  | .edge i => H.outer i '' I \ {H.pos i, H.pos (i + 1)}
  | .chord => H.chordParam '' I \ {H.pos 1, H.pos 4}
  | .face k => inside (H.arcOf k ∪ H.chordSet)
  | .aux _ => ∅

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.cellSet then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.cellSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.cellSet ``Submission.Schoenflies.HexData.cellSet

@[simp] theorem point_vert (i : Fin 6) : H.point (.vert i) = H.pos i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.point_vert then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.point_vert"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.point_vert ``Submission.Schoenflies.HexData.point_vert

@[simp] theorem draw_edge (i : Fin 6) : H.draw (.edge i) = H.outer i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.draw_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.draw_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.draw_edge ``Submission.Schoenflies.HexData.draw_edge

@[simp] theorem draw_chord : H.draw .chord = H.chordParam := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.draw_chord then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.draw_chord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.draw_chord ``Submission.Schoenflies.HexData.draw_chord

@[simp] theorem edgeArc_edge (i : Fin 6) :
    Graph.edgeArc H.draw (.edge i) = H.outer i '' I := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.edgeArc_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.edgeArc_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.edgeArc_edge ``Submission.Schoenflies.HexData.edgeArc_edge

@[simp] theorem edgeArc_chord : Graph.edgeArc H.draw .chord = H.chordParam '' I := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.edgeArc_chord then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.edgeArc_chord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.edgeArc_chord ``Submission.Schoenflies.HexData.edgeArc_chord

theorem pos_mem_outer (i : Fin 6) : H.pos i ∈ H.outer i '' I :=
  ⟨0, zero_mem_I, H.outer_zero i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.pos_mem_outer then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.pos_mem_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.pos_mem_outer ``Submission.Schoenflies.HexData.pos_mem_outer

theorem pos_succ_mem_outer (i : Fin 6) : H.pos (i + 1) ∈ H.outer i '' I :=
  ⟨1, one_mem_I, H.outer_one i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.pos_succ_mem_outer then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.pos_succ_mem_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.pos_succ_mem_outer ``Submission.Schoenflies.HexData.pos_succ_mem_outer

/-- **A vertex lies on an outer edge only if it is one of its two ends.** Not an axiom of
`HexData`: a vertex is an end of *its own* outer edge, so a vertex on a second edge is a point
of two edges, and the meeting condition places it among the ends of both. -/
theorem mem_outer_iff {k i : Fin 6} (h : H.pos k ∈ H.outer i '' I) : k = i ∨ k = i + 1 := by
  by_cases hki : k = i
  · exact Or.inl hki
  have hmeet := H.outer_meet k i hki ⟨H.pos_mem_outer k, h⟩
  rcases hmeet.2 with h' | h'
  · exact Or.inl (H.injective_pos h')
  · exact Or.inr (H.injective_pos h')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.mem_outer_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.mem_outer_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.mem_outer_iff ``Submission.Schoenflies.HexData.mem_outer_iff

/-- **A vertex lies on the crosscut only if it is one of its two ends.** -/
theorem mem_chord_iff {k : Fin 6} (h : H.pos k ∈ H.chordParam '' I) : k = 1 ∨ k = 4 := by
  rcases H.chord_meet k ⟨h, H.pos_mem_outer k⟩ with h' | h'
  · exact Or.inl (H.injective_pos h')
  · exact Or.inr (H.injective_pos h')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.mem_chord_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.mem_chord_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.mem_chord_iff ``Submission.Schoenflies.HexData.mem_chord_iff

theorem injOn_point : _root_.Set.InjOn H.point V(initSkel) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact congrArg InitialCell.vert (H.injective_pos hij)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.injOn_point then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.injOn_point"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.injOn_point ``Submission.Schoenflies.HexData.injOn_point

/-- The drawn skeleton: the pushforward of `initSkel` along the six positions. -/
theorem isDrawing : Graph.IsDrawing (initSkel.map H.point) H.draw where
  edge_param := by
    intro e he
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he
    rcases he with ⟨i, rfl⟩ | rfl
    · refine ⟨H.continuousOn_outer i, H.injOn_outer i, ?_⟩
      have : initSkel.IsLink (.edge i) (.vert i) (.vert (i + 1)) :=
        initSkel_isLink_ends (InitialCell.edge_mem_edges i)
      simpa [H.outer_zero i, H.outer_one i] using this.map H.point
    · refine ⟨H.continuousOn_chord, H.injOn_chord, ?_⟩
      have : initSkel.IsLink .chord (.vert 1) (.vert 4) :=
        initSkel_isLink_ends InitialCell.chord_mem_edges
      simpa [H.chord_zero, H.chord_one] using this.map H.point
  vertex_mem_edgeArc := by
    rintro e x y v hl ⟨_, ⟨k, rfl⟩, rfl⟩ hv
    obtain ⟨x', y', hl', rfl, rfl⟩ := hl
    obtain ⟨he, hxy⟩ := hl'
    rcases he with ⟨i, rfl⟩ | rfl
    · rcases H.mem_outer_iff (i := i) (k := k) hv with rfl | rfl <;>
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [InitialCell.ends]
    · rcases H.mem_chord_iff (k := k) hv with rfl | rfl <;>
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [InitialCell.ends]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he hf
    -- both ends of a 1-cell are among the six positions, so it suffices to name the index
    have key : ∀ (c : InitialCell) (k : Fin 6), c ∈ InitialCell.edges →
        H.pos k = H.point c.ends.1 ∨ H.pos k = H.point c.ends.2 →
        (initSkel.map H.point).Inc c (H.pos k) := by
      intro c k hc hk
      rw [Graph.map_inc]
      rcases hk with hk | hk
      · exact ⟨c.ends.1, ⟨c.ends.2, initSkel_isLink_ends hc⟩, hk⟩
      · exact ⟨c.ends.2, ⟨c.ends.1, (initSkel_isLink_ends hc).symm⟩, hk⟩
    have hmem : ∃ k : Fin 6, p = H.pos k ∧ (e = .chord ∨ ∃ i, e = .edge i ∧ (k = i ∨ k = i + 1))
        ∧ (f = .chord ∨ ∃ j, f = .edge j ∧ (k = j ∨ k = j + 1)) := by
      rcases he with ⟨i, rfl⟩ | rfl
      · rcases hf with ⟨j, rfl⟩ | rfl
        · have hij : i ≠ j := fun h => hef (by rw [h])
          obtain ⟨h1, h2⟩ := H.outer_meet i j hij ⟨hpe, hpf⟩
          rcases h1 with rfl | rfl
          · exact ⟨i, rfl, Or.inr ⟨i, rfl, Or.inl rfl⟩, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
          · exact ⟨i + 1, rfl, Or.inr ⟨i, rfl, Or.inr rfl⟩, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
        · rcases H.chord_meet i ⟨hpf, hpe⟩ with rfl | rfl
          · exact ⟨1, rfl, Or.inr ⟨i, rfl, H.mem_outer_iff hpe⟩, Or.inl rfl⟩
          · exact ⟨4, rfl, Or.inr ⟨i, rfl, H.mem_outer_iff hpe⟩, Or.inl rfl⟩
      · rcases hf with ⟨j, rfl⟩ | rfl
        · rcases H.chord_meet j ⟨hpe, hpf⟩ with rfl | rfl
          · exact ⟨1, rfl, Or.inl rfl, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
          · exact ⟨4, rfl, Or.inl rfl, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
        · exact absurd rfl hef
    obtain ⟨k, rfl, hke, hkf⟩ := hmem
    refine ⟨⟨.vert k, ⟨k, rfl⟩, rfl⟩, ?_, ?_⟩
    · rcases hke with rfl | ⟨i, rfl, hk⟩
      · rcases H.mem_chord_iff (k := k) hpe with rfl | rfl
        exacts [key _ _ InitialCell.chord_mem_edges (Or.inl rfl),
          key _ _ InitialCell.chord_mem_edges (Or.inr rfl)]
      · rcases hk with rfl | rfl
        exacts [key _ k (InitialCell.edge_mem_edges k) (Or.inl rfl),
          key _ (i + 1) (InitialCell.edge_mem_edges i) (Or.inr rfl)]
    · rcases hkf with rfl | ⟨j, rfl, hk⟩
      · rcases H.mem_chord_iff (k := k) hpf with rfl | rfl
        exacts [key _ _ InitialCell.chord_mem_edges (Or.inl rfl),
          key _ _ InitialCell.chord_mem_edges (Or.inr rfl)]
      · rcases hk with rfl | rfl
        exacts [key _ k (InitialCell.edge_mem_edges k) (Or.inl rfl),
          key _ (j + 1) (InitialCell.edge_mem_edges j) (Or.inr rfl)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.isDrawing then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.isDrawing"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.isDrawing ``Submission.Schoenflies.HexData.isDrawing

/-- **The realization of `initialStructure` determined by a `HexData`.** -/
def realization : initialStructure.Realization where
  pos := H.point
  drawing := H.draw
  injOn_pos := H.injOn_point
  isDrawing := H.isDrawing
  cell := H.cellSet
  cell_vertex := by rintro _ ⟨i, rfl⟩; rfl
  cell_edge := by
    rintro e x y ⟨he, hxy⟩
    rcases he with ⟨i, rfl⟩ | rfl <;>
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [cellSet, InitialCell.ends, Set.pair_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.realization then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.realization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.realization ``Submission.Schoenflies.HexData.realization

@[simp] theorem realization_pos : H.realization.pos = H.point := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.realization_pos then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.realization_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.realization_pos ``Submission.Schoenflies.HexData.realization_pos

@[simp] theorem realization_drawing : H.realization.drawing = H.draw := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.realization_drawing then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.realization_drawing"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.realization_drawing ``Submission.Schoenflies.HexData.realization_drawing

@[simp] theorem realization_cell : H.realization.cell = H.cellSet := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.realization_cell then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.realization_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.realization_cell ``Submission.Schoenflies.HexData.realization_cell

/-! #### The realized skeleton and the two boundary arcs -/

theorem pos_ne {i j : Fin 6} (h : i ≠ j) : H.pos i ≠ H.pos j :=
  fun he => h (H.injective_pos he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.pos_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.pos_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.pos_ne ``Submission.Schoenflies.HexData.pos_ne

theorem outer_meet_pair {i j : Fin 6} (hij : i ≠ j) {z : Plane} (hi : z ∈ H.outer i '' I)
    (hj : z ∈ H.outer j '' I) :
    (z = H.pos i ∨ z = H.pos (i + 1)) ∧ (z = H.pos j ∨ z = H.pos (j + 1)) :=
  H.outer_meet i j hij ⟨hi, hj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.outer_meet_pair then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.outer_meet_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.outer_meet_pair ``Submission.Schoenflies.HexData.outer_meet_pair

/-- Each outer edge is drawn as an arc between consecutive vertices. -/
theorem isArcBetween_outer (i : Fin 6) :
    IsArcBetween (H.outer i '' I) (H.pos i) (H.pos (i + 1)) :=
  ⟨H.outer i, H.continuousOn_outer i, H.injOn_outer i, rfl, H.outer_zero i, H.outer_one i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.isArcBetween_outer then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.isArcBetween_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.isArcBetween_outer ``Submission.Schoenflies.HexData.isArcBetween_outer

/-- The crosscut is drawn as an arc from `a` to `b`. -/
theorem isArcBetween_chordSet : IsArcBetween H.chordSet (H.pos 1) (H.pos 4) :=
  ⟨H.chordParam, H.continuousOn_chord, H.injOn_chord, rfl, H.chord_zero, H.chord_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.isArcBetween_chordSet then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.isArcBetween_chordSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.isArcBetween_chordSet ``Submission.Schoenflies.HexData.isArcBetween_chordSet

theorem outerArcs_eq :
    H.outerArcs = H.outer 0 '' I ∪ (H.outer 1 '' I ∪ (H.outer 2 '' I ∪ (H.outer 3 '' I ∪
      (H.outer 4 '' I ∪ H.outer 5 '' I)))) := by
  ext z
  simp only [outerArcs, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> tauto
  · rintro (h | h | h | h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.outerArcs_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.outerArcs_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.outerArcs_eq ``Submission.Schoenflies.HexData.outerArcs_eq

theorem arcOf_union : H.arcOf _root_.Bool.false ∪ H.arcOf _root_.Bool.true = H.outerArcs := by
  rw [outerArcs_eq]
  simp only [arcOf]
  ext z
  simp only [Set.mem_union]
  constructor <;> (intro h; tauto)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.arcOf_union then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.arcOf_union"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.arcOf_union ``Submission.Schoenflies.HexData.arcOf_union

/-- **`A₁` is an arc from `a` to `b`.** Three consecutive outer edges, glued at the two corner
vertices between them. -/
theorem arcOf_false_isArcBetween : IsArcBetween (H.arcOf _root_.Bool.false) (H.pos 1) (H.pos 4) := by
  have h23 : IsArcBetween (H.outer 2 '' I ∪ H.outer 3 '' I) (H.pos 2) (H.pos 4) := by
    refine (H.isArcBetween_outer 2).concatenate (H.isArcBetween_outer 3) fun z hz hz' => ?_
    obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 2) (j := 3) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  refine (H.isArcBetween_outer 1).concatenate h23 fun z hz hz' => ?_
  rcases hz' with hz' | hz'
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 1) (j := 2) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 1) (j := 3) (by decide) hz hz'
    rcases h₁ with rfl | rfl <;> rcases h₂ with h | h <;>
      exact absurd h (H.pos_ne (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.arcOf_false_isArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.arcOf_false_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.arcOf_false_isArcBetween ``Submission.Schoenflies.HexData.arcOf_false_isArcBetween

/-- **`A₂` is an arc from `b` to `a`.** -/
theorem arcOf_true_isArcBetween : IsArcBetween (H.arcOf _root_.Bool.true) (H.pos 4) (H.pos 1) := by
  have h50 : IsArcBetween (H.outer 5 '' I ∪ H.outer 0 '' I) (H.pos 5) (H.pos 1) := by
    refine (H.isArcBetween_outer 5).concatenate (H.isArcBetween_outer 0) fun z hz hz' => ?_
    obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 5) (j := 0) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  refine (H.isArcBetween_outer 4).concatenate h50 fun z hz hz' => ?_
  rcases hz' with hz' | hz'
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 4) (j := 5) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 4) (j := 0) (by decide) hz hz'
    rcases h₁ with rfl | rfl <;> rcases h₂ with h | h <;>
      exact absurd h (H.pos_ne (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.arcOf_true_isArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.arcOf_true_isArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.arcOf_true_isArcBetween ``Submission.Schoenflies.HexData.arcOf_true_isArcBetween

/-- **The two boundary arcs meet exactly at `a` and `b`.** Nine pairs of outer edges; six of
them have no vertex in common at all and contribute nothing. -/
theorem arcOf_inter : H.arcOf _root_.Bool.false ∩ H.arcOf _root_.Bool.true = ({H.pos 1, H.pos 4} : Set Plane) := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hz, hz'⟩
    simp only [arcOf, Set.mem_union] at hz hz'
    rcases hz with h₁ | h₁ | h₁ <;> rcases hz' with h₂ | h₂ | h₂ <;>
      · obtain ⟨ha, hb⟩ := H.outer_meet_pair (by decide) h₁ h₂
        rcases ha with rfl | rfl <;> rcases hb with h | h <;>
          first
            | exact Or.inl rfl
            | exact Or.inr rfl
            | exact absurd h (H.pos_ne (by decide))
  · rintro z (rfl | rfl)
    · refine ⟨Or.inl (H.pos_mem_outer 1), Or.inr (Or.inr ?_)⟩
      simpa using H.pos_succ_mem_outer 0
    · refine ⟨Or.inr (Or.inr ?_), Or.inl (H.pos_mem_outer 4)⟩
      simpa using H.pos_succ_mem_outer 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.arcOf_inter then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.arcOf_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.arcOf_inter ``Submission.Schoenflies.HexData.arcOf_inter

/-- The crosscut meets the outer cycle exactly at its two endpoints. -/
theorem chordSet_inter_outerArcs : H.chordSet ∩ H.outerArcs = ({H.pos 1, H.pos 4} : Set Plane) := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hz, hz'⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz'
    exact H.chord_meet i ⟨hz, hi⟩
  · rintro z (rfl | rfl)
    · exact ⟨by simpa [chordSet, H.chord_zero] using
        Set.mem_image_of_mem H.chordParam zero_mem_I, Set.mem_iUnion.2 ⟨1, H.pos_mem_outer 1⟩⟩
    · exact ⟨by simpa [chordSet, H.chord_one] using
        Set.mem_image_of_mem H.chordParam one_mem_I, Set.mem_iUnion.2 ⟨4, H.pos_mem_outer 4⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.chordSet_inter_outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.chordSet_inter_outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.chordSet_inter_outerArcs ``Submission.Schoenflies.HexData.chordSet_inter_outerArcs

theorem outerSet_realization : H.realization.outerSet = H.outerArcs := by
  change V(initOuter.map H.point) ∪ (⋃ e ∈ E(initOuter.map H.point), Graph.edgeArc H.draw e) = _
  refine Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [Graph.edgeSet_map, edgeSet_initOuter] at he
    obtain ⟨i, rfl⟩ := he
    exact Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i
  · refine Set.iUnion_subset fun i => ?_
    refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.edge i ∈ E(initOuter.map H.point) from ⟨i, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.outerSet_realization then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.outerSet_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.outerSet_realization ``Submission.Schoenflies.HexData.outerSet_realization

theorem skeletonSet_realization : H.realization.skeletonSet = H.outerArcs ∪ H.chordSet := by
  change V(initSkel.map H.point) ∪ (⋃ e ∈ E(initSkel.map H.point), Graph.edgeArc H.draw e) = _
  refine Subset.antisymm (Set.union_subset ?_ ?_) (Set.union_subset ?_ ?_)
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Or.inl (Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩)
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he
    rcases he with ⟨i, rfl⟩ | rfl
    · exact fun z hz => Or.inl (Set.mem_iUnion.2 ⟨i, hz⟩)
    · exact fun z hz => Or.inr hz
  · refine Set.iUnion_subset fun i => ?_
    refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.edge i ∈ E(initSkel.map H.point) from Or.inl ⟨i, rfl⟩)
  · refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.chord ∈ E(initSkel.map H.point) from Or.inr rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.skeletonSet_realization then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.skeletonSet_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.skeletonSet_realization ``Submission.Schoenflies.HexData.skeletonSet_realization

/-- **The open nonboundary part is the crosscut without its two endpoints.** With
`chord_meet` this is the connectedness clause of `def:admissible-graph` in one line: an arc
minus its endpoints is connected. -/
theorem nonboundary_realization : H.realization.nonboundary = H.chordSet \ H.outerArcs := by
  have h : H.realization.nonboundary = H.realization.skeletonSet \ H.realization.outerSet := rfl
  rw [h, H.skeletonSet_realization, H.outerSet_realization]
  ext z
  constructor
  · rintro ⟨h | h, h'⟩
    exacts [absurd h h', ⟨h, h'⟩]
  · rintro ⟨h, h'⟩
    exact ⟨Or.inr h, h'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.nonboundary_realization then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.nonboundary_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.nonboundary_realization ``Submission.Schoenflies.HexData.nonboundary_realization

/-- The open nonboundary part is the crosscut without its endpoints — the open arc. -/
theorem nonboundary_eq : H.realization.nonboundary = H.chordSet \ {H.pos 1, H.pos 4} := by
  rw [H.nonboundary_realization]
  ext z
  constructor
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, fun hmem => hz' ?_⟩
    have : z ∈ H.chordSet ∩ H.outerArcs := by rw [H.chordSet_inter_outerArcs]; exact hmem
    exact this.2
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, fun hmem => hz' ?_⟩
    have : z ∈ H.chordSet ∩ H.outerArcs := ⟨hz, hmem⟩
    rwa [H.chordSet_inter_outerArcs] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.nonboundary_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.nonboundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.nonboundary_eq ``Submission.Schoenflies.HexData.nonboundary_eq

/-- **The open nonboundary part is connected** — the last clause of `def:admissible-graph`.
With a single crosscut it is the open arc of the chord, a continuous injective image of
`(0, 1)`. -/
theorem isConnected_nonboundary : IsConnected H.realization.nonboundary := by
  rw [H.nonboundary_eq]
  have hopen : H.chordSet \ ({H.pos 1, H.pos 4} : Set Plane) = H.chordParam '' Set.Ioo 0 1 := by
    rw [chordSet, ← H.chord_zero, ← H.chord_one, ← openArc_eq_diff H.injOn_chord]
    rfl
  rw [hopen]
  refine (isConnected_Ioo (by norm_num : (0:ℝ) < 1)).image _ ?_
  exact H.continuousOn_chord.mono Ioo_subset_I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.isConnected_nonboundary then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.isConnected_nonboundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.isConnected_nonboundary ``Submission.Schoenflies.HexData.isConnected_nonboundary

end HexData


/-! ### The initial skeleton is 2-connected

The first clause of `def:admissible-graph`. It is a fact about the *abstract* graph — a hexagon
with one chord — and `Graph.isTwoConnected_map_iff` carries it to both realizations at once, so
it is proved here and nowhere else. The chord plays no part: the hexagon alone is 2-connected,
because deleting one of its vertices leaves a path. All the cyclic index arithmetic is
`decide`. -/

private theorem fin6_add_sub : ∀ k j : Fin 6, j = k + (j - k) := by decide

run_cmd do
  let target := ``Submission.Schoenflies.fin6_add_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.fin6_add_sub target :: scope.openDecls } }

private theorem fin6_add_one : ∀ k m : Fin 6, k + m + 1 = k + (m + 1) := by decide

run_cmd do
  let target := ``Submission.Schoenflies.fin6_add_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.fin6_add_one target :: scope.openDecls } }

private theorem fin6_add_eq_self : ∀ k n : Fin 6, k + n = k → n = 0 := by decide

run_cmd do
  let target := ``Submission.Schoenflies.fin6_add_eq_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.fin6_add_eq_self target :: scope.openDecls } }

private theorem stepFull {m m' : Fin 6} (h : m + 1 = m') :
    initSkel.Reaches (.vert m) (.vert m') := by
  subst h
  exact Graph.Reaches.of_isLink (initSkel_isLink_ends (InitialCell.edge_mem_edges m))

run_cmd do
  let target := ``Submission.Schoenflies.stepFull
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.stepFull target :: scope.openDecls } }

/-- The abstract hexagon-with-chord is connected. -/
theorem connected_initSkel : initSkel.Connected := by
  refine Graph.Connected.of_hub (u := .vert 0) ⟨0, rfl⟩ ?_
  rintro _ ⟨j, rfl⟩
  have s01 : initSkel.Reaches (.vert 0) (.vert 1) := stepFull (by decide)
  have s12 : initSkel.Reaches (.vert 1) (.vert 2) := stepFull (by decide)
  have s23 : initSkel.Reaches (.vert 2) (.vert 3) := stepFull (by decide)
  have s34 : initSkel.Reaches (.vert 3) (.vert 4) := stepFull (by decide)
  have s45 : initSkel.Reaches (.vert 4) (.vert 5) := stepFull (by decide)
  fin_cases j
  · exact Graph.Reaches.refl ⟨0, rfl⟩
  · exact s01
  · exact s01.trans s12
  · exact (s01.trans s12).trans s23
  · exact ((s01.trans s12).trans s23).trans s34
  · exact (((s01.trans s12).trans s23).trans s34).trans s45

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.connected_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.connected_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.connected_initSkel ``Submission.Schoenflies.connected_initSkel

private theorem vert_notMem_del {k n : Fin 6} (hn : n ≠ 0) :
    (InitialCell.vert (k + n)) ∉ ({InitialCell.vert k} : Set InitialCell) := by
  simp only [Set.mem_singleton_iff, InitialCell.vert.injEq]
  exact fun h => hn (fin6_add_eq_self k n h)

run_cmd do
  let target := ``Submission.Schoenflies.vert_notMem_del
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.vert_notMem_del target :: scope.openDecls } }

private theorem stepDel (k : Fin 6) {m m' : Fin 6} (hmm : m + 1 = m') (hm : m ≠ 0)
    (hm' : m' ≠ 0) :
    (initSkel.deleteVerts {InitialCell.vert k}).Reaches (.vert (k + m)) (.vert (k + m')) := by
  have h0 : initSkel.IsLink (InitialCell.edge (k + m)) (.vert (k + m)) (.vert (k + m + 1)) :=
    initSkel_isLink_ends (InitialCell.edge_mem_edges (k + m))
  rw [fin6_add_one k m, hmm] at h0
  refine Graph.Reaches.of_isLink (e := InitialCell.edge (k + m)) ?_
  rw [Graph.deleteVerts_isLink]
  exact ⟨h0, vert_notMem_del hm, vert_notMem_del hm'⟩

run_cmd do
  let target := ``Submission.Schoenflies.stepDel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.stepDel target :: scope.openDecls } }

/-- Deleting one vertex of the hexagon leaves a path, hence a connected graph. -/
theorem deleteVert_connected_initSkel (k : Fin 6) :
    (initSkel.deleteVerts {InitialCell.vert k}).Connected := by
  have h12 := stepDel k (m := 1) (m' := 2) (by decide) (by decide) (by decide)
  have h23 := stepDel k (m := 2) (m' := 3) (by decide) (by decide) (by decide)
  have h34 := stepDel k (m := 3) (m' := 4) (by decide) (by decide) (by decide)
  have h45 := stepDel k (m := 4) (m' := 5) (by decide) (by decide) (by decide)
  have hhub : (InitialCell.vert (k + 1)) ∈ V(initSkel.deleteVerts {InitialCell.vert k}) :=
    ⟨⟨k + 1, rfl⟩, vert_notMem_del (by decide)⟩
  refine Graph.Connected.of_hub hhub ?_
  rintro _ ⟨⟨j, rfl⟩, hj⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, fin6_add_sub k j⟩
  have hm : m ≠ 0 := by
    rintro rfl
    exact hj (by simp)
  fin_cases m
  · exact absurd rfl hm
  · exact Graph.Reaches.refl hhub
  · exact h12
  · exact h12.trans h23
  · exact (h12.trans h23).trans h34
  · exact ((h12.trans h23).trans h34).trans h45

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.deleteVert_connected_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.deleteVert_connected_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.deleteVert_connected_initSkel ``Submission.Schoenflies.deleteVert_connected_initSkel

/-- **The initial skeleton is 2-connected** — the first clause of `def:admissible-graph`. -/
theorem isTwoConnected_initSkel : initSkel.IsTwoConnected where
  hasThreeVertices :=
    ⟨.vert 0, ⟨0, rfl⟩, .vert 1, ⟨1, rfl⟩, .vert 2, ⟨2, rfl⟩, by decide, by decide, by decide⟩
  connected := connected_initSkel
  deleteVerts_connected := by rintro _ ⟨k, rfl⟩; exact deleteVert_connected_initSkel k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isTwoConnected_initSkel then
    throwError "Refusing to shadow existing declaration Schoenflies.isTwoConnected_initSkel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isTwoConnected_initSkel ``Submission.Schoenflies.isTwoConnected_initSkel

/-- **Both drawn skeleta are 2-connected.** By `lem:combinatorial-invariance` (a) there is only
one statement to prove, and it is the abstract one. -/
theorem HexData.isTwoConnected_graph (H : HexData) : (H.realization.graph).IsTwoConnected :=
  (Graph.isTwoConnected_map_iff H.injOn_point).2 isTwoConnected_initSkel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.HexData.isTwoConnected_graph then
    throwError "Refusing to shadow existing declaration Schoenflies.HexData.isTwoConnected_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.HexData.isTwoConnected_graph ``Submission.Schoenflies.HexData.isTwoConnected_graph

/-! ### The target realization: the square with one straight chord

The target side of `prop:initial-pair` is completely explicit. The six marked points of `S` are
the four corners together with `u(a) = (α, 1)` in the relative interior of the top side and
`u(b) = (β, -1)` in the relative interior of the bottom side, `|α|, |β| < 1`. **This is the one
place the nonadjacency hypothesis is used**: opposite sides, so the straight chord
`[(α,1), (β,-1)]` has every point other than its ends of sup norm `< 1`, hence in the open
square and off `S`.

All seven edges are straight, so each is pinned by one coordinate and swept by the other, and
the fifteen pairwise intersections are interval arithmetic. `hPiece` and `vPiece` are those two
shapes. -/

namespace Plane

/-- Two plane points agree when their coordinates do. -/
theorem eq_mk {p : Plane} {x y : ℝ} (h0 : p 0 = x) (h1 : p 1 = y) : p = Plane.mk x y := by
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.eq_mk then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.eq_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.eq_mk ``Submission.Schoenflies.Plane.eq_mk

theorem mk_inj {x y x' y' : ℝ} (h : Plane.mk x y = Plane.mk x' y') : x = x' ∧ y = y' :=
  ⟨congrArg (fun p : Plane => p 0) h, congrArg (fun p : Plane => p 1) h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.mk_inj then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.mk_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.mk_inj ``Submission.Schoenflies.Plane.mk_inj

end Plane

/-- A horizontal piece of the square boundary: second coordinate pinned, first coordinate
sweeping an interval. -/
def hPiece (c lo hi : ℝ) : Set Plane := {p : Plane | p 1 = c ∧ lo ≤ p 0 ∧ p 0 ≤ hi}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.hPiece then
    throwError "Refusing to shadow existing declaration Schoenflies.hPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.hPiece ``Submission.Schoenflies.hPiece

/-- A vertical piece of the square boundary. -/
def vPiece (c lo hi : ℝ) : Set Plane := {p : Plane | p 0 = c ∧ lo ≤ p 1 ∧ p 1 ≤ hi}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.vPiece then
    throwError "Refusing to shadow existing declaration Schoenflies.vPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.vPiece ``Submission.Schoenflies.vPiece

theorem segment_eq_hPiece (c : ℝ) {lo hi : ℝ} (h : lo ≤ hi) :
    segment ℝ (Plane.mk lo c) (Plane.mk hi c) = hPiece c lo hi := by
  ext p
  rw [mem_segment_horiz, segment_eq_Icc h]
  simp [hPiece, Set.mem_Icc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.segment_eq_hPiece then
    throwError "Refusing to shadow existing declaration Schoenflies.segment_eq_hPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.segment_eq_hPiece ``Submission.Schoenflies.segment_eq_hPiece

theorem segment_eq_vPiece (c : ℝ) {lo hi : ℝ} (h : lo ≤ hi) :
    segment ℝ (Plane.mk c lo) (Plane.mk c hi) = vPiece c lo hi := by
  ext p
  rw [mem_segment_vert, segment_eq_Icc h]
  simp [vPiece, Set.mem_Icc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.segment_eq_vPiece then
    throwError "Refusing to shadow existing declaration Schoenflies.segment_eq_vPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.segment_eq_vPiece ``Submission.Schoenflies.segment_eq_vPiece

theorem hPiece_subset_modelCurve {c lo hi : ℝ} (hc : |c| = 1) (hlo : -1 ≤ lo) (hhi : hi ≤ 1) :
    hPiece c lo hi ⊆ modelCurve := by
  rintro p ⟨h1, h2, h3⟩
  change Plane.supNorm p = 1
  simp only [Plane.supNorm, h1, hc]
  exact max_eq_right (by rw [abs_le]; constructor <;> linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.hPiece_subset_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.hPiece_subset_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.hPiece_subset_modelCurve ``Submission.Schoenflies.hPiece_subset_modelCurve

theorem vPiece_subset_modelCurve {c lo hi : ℝ} (hc : |c| = 1) (hlo : -1 ≤ lo) (hhi : hi ≤ 1) :
    vPiece c lo hi ⊆ modelCurve := by
  rintro p ⟨h1, h2, h3⟩
  change Plane.supNorm p = 1
  simp only [Plane.supNorm, h1, hc]
  exact max_eq_left (by rw [abs_le]; constructor <;> linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.vPiece_subset_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.vPiece_subset_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.vPiece_subset_modelCurve ``Submission.Schoenflies.vPiece_subset_modelCurve

variable {α β : ℝ}

/-- The six marked points of `S`, in cyclic order: the corner `(1,1)`, `u(a) = (α,1)`, the
corners `(-1,1)` and `(-1,-1)`, `u(b) = (β,-1)`, and the corner `(1,-1)`. -/
def tgtPos (α β : ℝ) : Fin 6 → Plane :=
  ![Plane.mk 1 1, Plane.mk α 1, Plane.mk (-1) 1, Plane.mk (-1) (-1), Plane.mk β (-1),
    Plane.mk 1 (-1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtPos then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtPos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtPos ``Submission.Schoenflies.tgtPos

/-- The six outer edges of the target, straight. -/
noncomputable def tgtOuter (α β : ℝ) (i : Fin 6) : ℝ → Plane :=
  AffineMap.lineMap (tgtPos α β i) (tgtPos α β (i + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtOuter then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtOuter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtOuter ``Submission.Schoenflies.tgtOuter

/-- The straight chord `[u(a), u(b)]`. -/
noncomputable def tgtChord (α β : ℝ) : ℝ → Plane :=
  AffineMap.lineMap (tgtPos α β 1) (tgtPos α β 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtChord then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtChord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtChord ``Submission.Schoenflies.tgtChord

theorem tgtOuter_image (α β : ℝ) (i : Fin 6) :
    tgtOuter α β i '' I = segment ℝ (tgtPos α β i) (tgtPos α β (i + 1)) := by
  rw [segment_eq_image_lineMap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtOuter_image then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtOuter_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtOuter_image ``Submission.Schoenflies.tgtOuter_image

theorem tgtChord_image (α β : ℝ) :
    tgtChord α β '' I = segment ℝ (Plane.mk α 1) (Plane.mk β (-1)) := by
  rw [segment_eq_image_lineMap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtChord_image then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtChord_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtChord_image ``Submission.Schoenflies.tgtChord_image

/-- The six target arcs, in the pinned-coordinate normal form. -/
theorem segment_tgtPos (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    segment ℝ (tgtPos α β i) (tgtPos α β (i + 1)) =
      ![hPiece 1 α 1, hPiece 1 (-1) α, vPiece (-1) (-1) 1, hPiece (-1) (-1) β, hPiece (-1) β 1,
        vPiece 1 (-1) 1] i := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  fin_cases i
  · change segment ℝ (Plane.mk 1 1) (Plane.mk α 1) = hPiece 1 α 1
    rw [segment_symm, segment_eq_hPiece 1 hα2.le]
  · change segment ℝ (Plane.mk α 1) (Plane.mk (-1) 1) = hPiece 1 (-1) α
    rw [segment_symm, segment_eq_hPiece 1 hα1.le]
  · change segment ℝ (Plane.mk (-1) 1) (Plane.mk (-1) (-1)) = vPiece (-1) (-1) 1
    rw [segment_symm, segment_eq_vPiece (-1) (by norm_num : (-1:ℝ) ≤ 1)]
  · change segment ℝ (Plane.mk (-1) (-1)) (Plane.mk β (-1)) = hPiece (-1) (-1) β
    rw [segment_eq_hPiece (-1) hβ1.le]
  · change segment ℝ (Plane.mk β (-1)) (Plane.mk 1 (-1)) = hPiece (-1) β 1
    rw [segment_eq_hPiece (-1) hβ2.le]
  · change segment ℝ (Plane.mk 1 (-1)) (Plane.mk 1 1) = vPiece 1 (-1) 1
    rw [segment_eq_vPiece 1 (by norm_num : (-1:ℝ) ≤ 1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.segment_tgtPos then
    throwError "Refusing to shadow existing declaration Schoenflies.segment_tgtPos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.segment_tgtPos ``Submission.Schoenflies.segment_tgtPos

theorem injective_tgtPos (hα : |α| < 1) (hβ : |β| < 1) : Function.Injective (tgtPos α β) := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; obtain ⟨h0, h1⟩ := Plane.mk_inj h; linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.injective_tgtPos then
    throwError "Refusing to shadow existing declaration Schoenflies.injective_tgtPos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.injective_tgtPos ``Submission.Schoenflies.injective_tgtPos

theorem tgtOuter_subset_modelCurve (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtOuter α β i '' I ⊆ modelCurve := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  rw [tgtOuter_image, segment_tgtPos hα hβ]
  fin_cases i
  exacts [hPiece_subset_modelCurve (by norm_num) hα1.le le_rfl,
    hPiece_subset_modelCurve (by norm_num) le_rfl hα2.le,
    vPiece_subset_modelCurve (by norm_num) le_rfl le_rfl,
    hPiece_subset_modelCurve (by norm_num) le_rfl hβ2.le,
    hPiece_subset_modelCurve (by norm_num) hβ1.le le_rfl,
    vPiece_subset_modelCurve (by norm_num) le_rfl le_rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtOuter_subset_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtOuter_subset_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtOuter_subset_modelCurve ``Submission.Schoenflies.tgtOuter_subset_modelCurve

/-- **The fifteen pairwise intersections of the six target edges.** Two edges on the same side
of the square overlap in at most the marked point between them; two on adjacent sides meet at
most in the corner they share, and the four cases where a corner is not on the piece in
question are empty because `|α|, |β| < 1`; two on opposite sides never meet. Every one of them
is a comparison of two real intervals. -/
theorem tgtOuter_meet (hα : |α| < 1) (hβ : |β| < 1) (i j : Fin 6) (hij : i ≠ j) :
    tgtOuter α β i '' I ∩ tgtOuter α β j '' I ⊆
      ({tgtPos α β i, tgtPos α β (i + 1)} : Set Plane) ∩
        {tgtPos α β j, tgtPos α β (j + 1)} := by
  have hα' := abs_lt.1 hα
  have hβ' := abs_lt.1 hβ
  obtain ⟨hα1, hα2⟩ := hα'
  obtain ⟨hβ1, hβ2⟩ := hβ'
  simp only [tgtOuter_image, segment_tgtPos hα hβ]
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | · rintro p ⟨⟨e1, e2, e3⟩, f1, f2, f3⟩
          first
            | (exfalso; linarith)
            | exact ⟨Or.inl (Plane.eq_mk (by linarith) (by linarith)),
                Or.inl (Plane.eq_mk (by linarith) (by linarith))⟩
            | exact ⟨Or.inl (Plane.eq_mk (by linarith) (by linarith)),
                Or.inr (Plane.eq_mk (by linarith) (by linarith))⟩
            | exact ⟨Or.inr (Plane.eq_mk (by linarith) (by linarith)),
                Or.inl (Plane.eq_mk (by linarith) (by linarith))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtOuter_meet then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtOuter_meet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtOuter_meet ``Submission.Schoenflies.tgtOuter_meet

/-- **The straight chord between opposite sides has all its other points in the open square.**
This is the single use of the nonadjacency hypothesis of `prop:initial-pair`. -/
theorem openSegment_chord_supNorm_lt (hα : |α| < 1) (hβ : |β| < 1) :
    ∀ p ∈ openSegment ℝ (Plane.mk α 1) (Plane.mk β (-1)), Plane.supNorm p < 1 := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  rintro p ⟨a, b, ha, hb, hab, rfl⟩
  have h0 : (a • Plane.mk α 1 + b • Plane.mk β (-1)) 0 = a * α + b * β := by
    rw [Plane.smul_add_apply]; simp
  have h1 : (a • Plane.mk α 1 + b • Plane.mk β (-1)) 1 = a - b := by
    rw [Plane.smul_add_apply]; simp; ring
  have hb0 : |a * α + b * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hb1 : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [Plane.supNorm, h0, h1]
  exact max_lt hb0 hb1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openSegment_chord_supNorm_lt then
    throwError "Refusing to shadow existing declaration Schoenflies.openSegment_chord_supNorm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openSegment_chord_supNorm_lt ``Submission.Schoenflies.openSegment_chord_supNorm_lt

theorem openSegment_chord_notMem_modelCurve (hα : |α| < 1) (hβ : |β| < 1) :
    ∀ p ∈ openSegment ℝ (Plane.mk α 1) (Plane.mk β (-1)), p ∉ modelCurve := fun p hp hmem =>
  absurd (show Plane.supNorm p = 1 from hmem)
    (ne_of_lt (openSegment_chord_supNorm_lt hα hβ p hp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openSegment_chord_notMem_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.openSegment_chord_notMem_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openSegment_chord_notMem_modelCurve ``Submission.Schoenflies.openSegment_chord_notMem_modelCurve

/-- The chord meets each outer edge only at its own two ends. -/
theorem tgtChord_meet (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtChord α β '' I ∩ tgtOuter α β i '' I ⊆
      ({tgtPos α β 1, tgtPos α β 4} : Set Plane) := by
  rintro p ⟨hp, hp'⟩
  rw [tgtChord_image, ← insert_endpoints_openSegment] at hp
  rcases hp with rfl | rfl | hp
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (tgtOuter_subset_modelCurve hα hβ i hp')
      (openSegment_chord_notMem_modelCurve hα hβ _ hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtChord_meet then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtChord_meet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtChord_meet ``Submission.Schoenflies.tgtChord_meet

theorem tgtOuter_image_eq (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtOuter α β i '' I =
      ![hPiece 1 α 1, hPiece 1 (-1) α, vPiece (-1) (-1) 1, hPiece (-1) (-1) β, hPiece (-1) β 1,
        vPiece 1 (-1) 1] i := by
  rw [tgtOuter_image, segment_tgtPos hα hβ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtOuter_image_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtOuter_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtOuter_image_eq ``Submission.Schoenflies.tgtOuter_image_eq

/-- **The six target edges cover `S`.** Each side of the square is one piece, except the top
and the bottom, which are cut in two at `u(a)` and `u(b)`. -/
theorem iUnion_tgtOuter (hα : |α| < 1) (hβ : |β| < 1) :
    (⋃ i : Fin 6, tgtOuter α β i '' I) = modelCurve := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  refine Subset.antisymm (Set.iUnion_subset (tgtOuter_subset_modelCurve hα hβ)) fun p hp => ?_
  rw [modelCurve_eq_sides] at hp
  rcases hp with (hp | hp) | (hp | hp)
  · rw [mem_sideTop, abs_le] at hp
    obtain ⟨h1, h0⟩ := hp
    rcases le_or_gt α (p 0) with h | h
    · exact Set.mem_iUnion.2 ⟨0, by rw [tgtOuter_image_eq hα hβ 0]; exact ⟨h1, h, h0.2⟩⟩
    · exact Set.mem_iUnion.2 ⟨1, by rw [tgtOuter_image_eq hα hβ 1]; exact ⟨h1, h0.1, h.le⟩⟩
  · rw [mem_sideLeft, abs_le] at hp
    obtain ⟨h0, h1⟩ := hp
    exact Set.mem_iUnion.2 ⟨2, by rw [tgtOuter_image_eq hα hβ 2]; exact ⟨h0, h1.1, h1.2⟩⟩
  · rw [mem_sideBottom, abs_le] at hp
    obtain ⟨h1, h0⟩ := hp
    rcases le_or_gt (p 0) β with h | h
    · exact Set.mem_iUnion.2 ⟨3, by rw [tgtOuter_image_eq hα hβ 3]; exact ⟨h1, h0.1, h⟩⟩
    · exact Set.mem_iUnion.2 ⟨4, by rw [tgtOuter_image_eq hα hβ 4]; exact ⟨h1, h.le, h0.2⟩⟩
  · rw [mem_sideRight, abs_le] at hp
    obtain ⟨h0, h1⟩ := hp
    exact Set.mem_iUnion.2 ⟨5, by rw [tgtOuter_image_eq hα hβ 5]; exact ⟨h0, h1.1, h1.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.iUnion_tgtOuter then
    throwError "Refusing to shadow existing declaration Schoenflies.iUnion_tgtOuter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.iUnion_tgtOuter ``Submission.Schoenflies.iUnion_tgtOuter

theorem tgtPos_mem_modelCurve (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtPos α β i ∈ modelCurve := by
  refine tgtOuter_subset_modelCurve hα hβ i ⟨0, zero_mem_I, ?_⟩
  exact AffineMap.lineMap_apply_zero _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtPos_mem_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtPos_mem_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtPos_mem_modelCurve ``Submission.Schoenflies.tgtPos_mem_modelCurve

theorem tgtPos_succ_ne (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtPos α β i ≠ tgtPos α β (i + 1) := by
  have hne : i ≠ i + 1 := by revert i; decide
  exact fun h => hne (injective_tgtPos hα hβ h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.tgtPos_succ_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.tgtPos_succ_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.tgtPos_succ_ne ``Submission.Schoenflies.tgtPos_succ_ne

/-- **The target realization of `prop:initial-pair`**: the square `S`, subdivided at its four
corners and at `u(a) = (α,1)`, `u(b) = (β,-1)`, together with the straight chord between the
last two. -/
noncomputable def targetHex (hα : |α| < 1) (hβ : |β| < 1) : HexData where
  pos := tgtPos α β
  outer := tgtOuter α β
  chordParam := tgtChord α β
  injective_pos := injective_tgtPos hα hβ
  continuousOn_outer := fun _ => AffineMap.lineMap_continuous.continuousOn
  injOn_outer := fun i => injOn_lineMap (tgtPos_succ_ne hα hβ i)
  outer_zero := fun i => AffineMap.lineMap_apply_zero _ _
  outer_one := fun i => AffineMap.lineMap_apply_one _ _
  continuousOn_chord := AffineMap.lineMap_continuous.continuousOn
  injOn_chord := injOn_lineMap (by
    intro h
    have := injective_tgtPos hα hβ h
    exact absurd this (by decide))
  chord_zero := AffineMap.lineMap_apply_zero _ _
  chord_one := AffineMap.lineMap_apply_one _ _
  outer_meet := tgtOuter_meet hα hβ
  chord_meet := tgtChord_meet hα hβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.targetHex then
    throwError "Refusing to shadow existing declaration Schoenflies.targetHex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.targetHex ``Submission.Schoenflies.targetHex

@[simp] theorem targetHex_pos (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).pos = tgtPos α β := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.targetHex_pos then
    throwError "Refusing to shadow existing declaration Schoenflies.targetHex_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.targetHex_pos ``Submission.Schoenflies.targetHex_pos

@[simp] theorem targetHex_outer (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).outer = tgtOuter α β := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.targetHex_outer then
    throwError "Refusing to shadow existing declaration Schoenflies.targetHex_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.targetHex_outer ``Submission.Schoenflies.targetHex_outer

@[simp] theorem targetHex_chordParam (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).chordParam = tgtChord α β := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.targetHex_chordParam then
    throwError "Refusing to shadow existing declaration Schoenflies.targetHex_chordParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.targetHex_chordParam ``Submission.Schoenflies.targetHex_chordParam

/-- **The target outer cycle is exactly `S`.** -/
theorem targetHex_outerArcs (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).outerArcs = modelCurve := iUnion_tgtOuter hα hβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.targetHex_outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.targetHex_outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.targetHex_outerArcs ``Submission.Schoenflies.targetHex_outerArcs


/-! ### The source realization: the curve with one polygonal crosscut

The source realization is the pushforward of the target's outer cycle along `w = u⁻¹`, together
with the polygonal crosscut `P` as its seventh edge. Nothing about the six outer arcs has to be
proved again: `w` is injective on `S`, so each of the three drawing conditions transfers.

The crosscut arrives as a parametrization together with the one geometric fact `lem:accessible-
endpoints` supplies — that every point of it other than its two ends lies in `D` — from which
`P ∩ C = {a, b}` follows, and with it the last meeting condition. -/

variable {C : Set Plane}

/-- **The source realization of `prop:initial-pair`**: `C`, subdivided at the `u`-preimages of
the four corners and of `u(a), u(b)`, together with the polygonal crosscut `P` from `a` to
`b`. -/
noncomputable def sourceHex {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : _root_.Set.InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) : HexData where
  pos := fun i => w (tgtPos α β i)
  outer := fun i t => w (tgtOuter α β i t)
  chordParam := sp
  injective_pos := fun i j h =>
    injective_tgtPos hα hβ
      (hw.injOn_inv (tgtPos_mem_modelCurve hα hβ i) (tgtPos_mem_modelCurve hα hβ j) h)
  continuousOn_outer := fun i =>
    hw.continuousOn_inv.comp AffineMap.lineMap_continuous.continuousOn
      fun t ht => tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
  injOn_outer := fun i =>
    hw.injOn_inv.comp (injOn_lineMap (tgtPos_succ_ne hα hβ i))
      fun t ht => tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
  outer_zero := fun i => congrArg w (AffineMap.lineMap_apply_zero _ _)
  outer_one := fun i => congrArg w (AffineMap.lineMap_apply_one _ _)
  continuousOn_chord := hspc
  injOn_chord := hspi
  chord_zero := hsp0
  chord_one := hsp1
  outer_meet := by
    rintro i j hij z ⟨⟨s, hs, rfl⟩, t, ht, hzt⟩
    -- the two preimages lie on `S`, where `w` is injective, so they coincide
    have hsm : tgtOuter α β i s ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ i ⟨s, hs, rfl⟩
    have htm : tgtOuter α β j t ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ j ⟨t, ht, rfl⟩
    have heq : tgtOuter α β j t = tgtOuter α β i s := hw.injOn_inv htm hsm hzt
    obtain ⟨h₁, h₂⟩ := tgtOuter_meet hα hβ i j hij ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
    constructor
    · rcases h₁ with h | h
      exacts [Or.inl (congrArg w h), Or.inr (congrArg w h)]
    · rcases h₂ with h | h
      exacts [Or.inl (congrArg w h), Or.inr (congrArg w h)]
  chord_meet := by
    rintro i z ⟨hz, t, ht, rfl⟩
    by_contra hzc
    have hmem : tgtOuter α β i t ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
    exact inside_subset_compl (hspin ⟨hz, hzc⟩) (hw.mapsTo_inv hmem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sourceHex then
    throwError "Refusing to shadow existing declaration Schoenflies.sourceHex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sourceHex ``Submission.Schoenflies.sourceHex

@[simp] theorem sourceHex_pos {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : _root_.Set.InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).pos = fun i => w (tgtPos α β i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sourceHex_pos then
    throwError "Refusing to shadow existing declaration Schoenflies.sourceHex_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sourceHex_pos ``Submission.Schoenflies.sourceHex_pos

@[simp] theorem sourceHex_chordParam {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : _root_.Set.InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).chordParam = sp := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sourceHex_chordParam then
    throwError "Refusing to shadow existing declaration Schoenflies.sourceHex_chordParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sourceHex_chordParam ``Submission.Schoenflies.sourceHex_chordParam

/-- **The source outer cycle is exactly `C`.** -/
theorem sourceHex_outerArcs {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : _root_.Set.InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).outerArcs = C := by
  have : (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).outerArcs =
      w '' (⋃ i : Fin 6, tgtOuter α β i '' I) := by
    rw [Set.image_iUnion]
    refine Set.iUnion_congr fun i => ?_
    rw [← Set.image_comp]
    rfl
  rw [this, iUnion_tgtOuter hα hβ, hw.image_inv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sourceHex_outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.sourceHex_outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sourceHex_outerArcs ``Submission.Schoenflies.sourceHex_outerArcs


/-! ### The skeleton homeomorphism

`g` is `u` on `C` and a chosen homeomorphism `P → [u(a), u(b)]` on the crosscut. The chosen
homeomorphism is the one that matches the parameters: `sp t ↦ [u(a), u(b)](t)`. The two
definitions agree at `a` and `b`, which is where `C` and `P` meet, so the pasting lemma applies
to the two closed pieces of the skeleton. -/

/-- A continuous injection of a compact set has a continuous inverse on its image. Stated for
the set-level `Function.invFunOn`, which is what a parametrized arc has to be inverted with. -/
theorem continuousOn_invFunOn_image {f : ℝ → Plane} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : _root_.Set.InjOn f s) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro F hF
  refine ⟨f '' (F ∩ s), (hs.inter_left hF).image_of_continuousOn (hf.mono _root_.Set.inter_subset_right)
    |>.isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    rw [_root_.Set.mem_preimage, hinj.leftInvOn_invFunOn hx] at hy
    exact ⟨⟨x, ⟨hy, hx⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨x, ⟨hxF, hxs⟩, rfl⟩, -⟩
    exact ⟨by rw [_root_.Set.mem_preimage, hinj.leftInvOn_invFunOn hxs]; exact hxF, ⟨x, hxs, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.continuousOn_invFunOn_image then
    throwError "Refusing to shadow existing declaration Schoenflies.continuousOn_invFunOn_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.continuousOn_invFunOn_image ``Submission.Schoenflies.continuousOn_invFunOn_image

/-! ### The initial matched pair, bundled

`InitialData C` is the data `prop:initial-pair` produces before any of its conclusions are
drawn: the boundary homeomorphism `u` with its inverse `w`, the two abscissae `xa, xb` of
`u(a)` and `u(b)` on the two opposite sides, and the polygonal crosscut as a parametrization.
Both realizations, the skeleton homeomorphism, and every conclusion below are functions of
it. -/

/-- The data of an initial matched pair over the Jordan curve `C`. -/
structure InitialData (C : Set Plane) where
  /-- The boundary homeomorphism `u : C → S` of the blueprint. -/
  u : Plane → Plane
  /-- Its inverse. -/
  w : Plane → Plane
  /-- `u` maps `C` homeomorphically onto the model curve. -/
  homeo : IsSetHomeoOn u w C modelCurve
  /-- `C` is a Jordan curve. -/
  curve : IsJordanCurve C
  /-- The abscissa of `u(a)` on the top side. -/
  xa : ℝ
  /-- The abscissa of `u(b)` on the bottom side. -/
  xb : ℝ
  /-- `u(a)` is interior to the top side. -/
  abs_xa : |xa| < 1
  /-- `u(b)` is interior to the bottom side — the *opposite* side. -/
  abs_xb : |xb| < 1
  /-- The crosscut, as a parametrization. -/
  cross : ℝ → Plane
  /-- The crosscut is drawn continuously. -/
  continuousOn_cross : ContinuousOn cross I
  /-- The crosscut is simple. -/
  injOn_cross : _root_.Set.InjOn cross I
  /-- The crosscut starts at `a`. -/
  cross_zero : cross 0 = w (tgtPos xa xb 1)
  /-- The crosscut ends at `b`. -/
  cross_one : cross 1 = w (tgtPos xa xb 4)
  /-- Every other point of the crosscut is inside `C` — `lem:accessible-endpoints`. -/
  cross_inside : cross '' I \ {w (tgtPos xa xb 1), w (tgtPos xa xb 4)} ⊆ inside C
  /-- The crosscut is polygonal. -/
  polygonal_cross : IsPolygonal (cross '' I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData ``Submission.Schoenflies.InitialData

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-- The first chosen boundary point, `a = u⁻¹(xa, 1)`. -/
def a : Plane := d.w (tgtPos d.xa d.xb 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.a then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.a"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.a ``Submission.Schoenflies.InitialData.a

/-- The second chosen boundary point, `b = u⁻¹(xb, -1)`. -/
def b : Plane := d.w (tgtPos d.xa d.xb 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.b then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.b"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.b ``Submission.Schoenflies.InitialData.b

/-- The polygonal crosscut `P`, as a set. -/
def crossSet : Set Plane := d.cross '' I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.crossSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.crossSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.crossSet ``Submission.Schoenflies.InitialData.crossSet

/-- **The source realization data.** -/
noncomputable def src : HexData :=
  sourceHex d.homeo d.abs_xa d.abs_xb d.continuousOn_cross d.injOn_cross d.cross_zero
    d.cross_one d.cross_inside

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.src then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.src"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.src ``Submission.Schoenflies.InitialData.src

/-- **The target realization data.** -/
noncomputable def tgt : HexData := targetHex d.abs_xa d.abs_xb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgt then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgt"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgt ``Submission.Schoenflies.InitialData.tgt

/-- **The source realization of `initialStructure`** — `Γ` of `prop:initial-pair`. -/
noncomputable def sourceRealization : initialStructure.Realization := d.src.realization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.sourceRealization then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.sourceRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.sourceRealization ``Submission.Schoenflies.InitialData.sourceRealization

/-- **The target realization of `initialStructure`** — `Γ'` of `prop:initial-pair`. -/
noncomputable def targetRealization : initialStructure.Realization := d.tgt.realization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.targetRealization then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.targetRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.targetRealization ``Submission.Schoenflies.InitialData.targetRealization

@[simp] theorem src_pos_one : d.src.pos 1 = d.a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.src_pos_one then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.src_pos_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.src_pos_one ``Submission.Schoenflies.InitialData.src_pos_one

@[simp] theorem src_pos_four : d.src.pos 4 = d.b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.src_pos_four then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.src_pos_four"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.src_pos_four ``Submission.Schoenflies.InitialData.src_pos_four

@[simp] theorem src_chordSet : d.src.chordSet = d.crossSet := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.src_chordSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.src_chordSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.src_chordSet ``Submission.Schoenflies.InitialData.src_chordSet

@[simp] theorem tgt_pos_one : d.tgt.pos 1 = Plane.mk d.xa 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgt_pos_one then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgt_pos_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgt_pos_one ``Submission.Schoenflies.InitialData.tgt_pos_one

@[simp] theorem tgt_pos_four : d.tgt.pos 4 = Plane.mk d.xb (-1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgt_pos_four then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgt_pos_four"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgt_pos_four ``Submission.Schoenflies.InitialData.tgt_pos_four

theorem tgt_chordSet : d.tgt.chordSet = segment ℝ (Plane.mk d.xa 1) (Plane.mk d.xb (-1)) :=
  tgtChord_image d.xa d.xb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgt_chordSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgt_chordSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgt_chordSet ``Submission.Schoenflies.InitialData.tgt_chordSet

theorem src_outerArcs : d.src.outerArcs = C :=
  sourceHex_outerArcs d.homeo d.abs_xa d.abs_xb d.continuousOn_cross d.injOn_cross d.cross_zero
    d.cross_one d.cross_inside

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.src_outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.src_outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.src_outerArcs ``Submission.Schoenflies.InitialData.src_outerArcs

theorem tgt_outerArcs : d.tgt.outerArcs = modelCurve := targetHex_outerArcs d.abs_xa d.abs_xb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgt_outerArcs then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgt_outerArcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgt_outerArcs ``Submission.Schoenflies.InitialData.tgt_outerArcs

theorem a_mem : d.a ∈ C := d.homeo.mapsTo_inv (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.a_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.a_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.a_mem ``Submission.Schoenflies.InitialData.a_mem

theorem b_mem : d.b ∈ C := d.homeo.mapsTo_inv (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.b_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.b_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.b_mem ``Submission.Schoenflies.InitialData.b_mem

theorem u_a : d.u (d.w (tgtPos d.xa d.xb 1)) = tgtPos d.xa d.xb 1 :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.u_a then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.u_a"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.u_a ``Submission.Schoenflies.InitialData.u_a

theorem u_b : d.u (d.w (tgtPos d.xa d.xb 4)) = tgtPos d.xa d.xb 4 :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.u_b then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.u_b"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.u_b ``Submission.Schoenflies.InitialData.u_b

@[simp] theorem u_apply_a : d.u d.a = Plane.mk d.xa 1 := d.u_a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.u_apply_a then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.u_apply_a"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.u_apply_a ``Submission.Schoenflies.InitialData.u_apply_a

@[simp] theorem u_apply_b : d.u d.b = Plane.mk d.xb (-1) := d.u_b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.u_apply_b then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.u_apply_b"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.u_apply_b ``Submission.Schoenflies.InitialData.u_apply_b

theorem sourceRealization_skeletonSet : d.sourceRealization.skeletonSet = C ∪ d.crossSet := by
  rw [sourceRealization, HexData.skeletonSet_realization, d.src_outerArcs]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.sourceRealization_skeletonSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.sourceRealization_skeletonSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.sourceRealization_skeletonSet ``Submission.Schoenflies.InitialData.sourceRealization_skeletonSet

theorem targetRealization_skeletonSet :
    d.targetRealization.skeletonSet = modelCurve ∪ d.tgt.chordSet := by
  rw [targetRealization, HexData.skeletonSet_realization, d.tgt_outerArcs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.targetRealization_skeletonSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.targetRealization_skeletonSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.targetRealization_skeletonSet ``Submission.Schoenflies.InitialData.targetRealization_skeletonSet

theorem sourceRealization_outerSet : d.sourceRealization.outerSet = C := by
  rw [sourceRealization, HexData.outerSet_realization, d.src_outerArcs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.sourceRealization_outerSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.sourceRealization_outerSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.sourceRealization_outerSet ``Submission.Schoenflies.InitialData.sourceRealization_outerSet

theorem targetRealization_outerSet : d.targetRealization.outerSet = modelCurve := by
  rw [targetRealization, HexData.outerSet_realization, d.tgt_outerArcs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.targetRealization_outerSet then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.targetRealization_outerSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.targetRealization_outerSet ``Submission.Schoenflies.InitialData.targetRealization_outerSet

theorem isConnected_sourceRealization_nonboundary :
    IsConnected d.sourceRealization.nonboundary := d.src.isConnected_nonboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isConnected_sourceRealization_nonboundary then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isConnected_sourceRealization_nonboundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isConnected_sourceRealization_nonboundary ``Submission.Schoenflies.InitialData.isConnected_sourceRealization_nonboundary

theorem isConnected_targetRealization_nonboundary :
    IsConnected d.targetRealization.nonboundary := d.tgt.isConnected_nonboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isConnected_targetRealization_nonboundary then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isConnected_targetRealization_nonboundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isConnected_targetRealization_nonboundary ``Submission.Schoenflies.InitialData.isConnected_targetRealization_nonboundary

theorem isTwoConnected_sourceRealization : (d.sourceRealization.graph).IsTwoConnected :=
  d.src.isTwoConnected_graph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isTwoConnected_sourceRealization then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isTwoConnected_sourceRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isTwoConnected_sourceRealization ``Submission.Schoenflies.InitialData.isTwoConnected_sourceRealization

theorem isTwoConnected_targetRealization : (d.targetRealization.graph).IsTwoConnected :=
  d.tgt.isTwoConnected_graph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isTwoConnected_targetRealization then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isTwoConnected_targetRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isTwoConnected_targetRealization ``Submission.Schoenflies.InitialData.isTwoConnected_targetRealization

/-! #### `a` and `b` are the only points the crosscut shares with the curve -/

theorem cross_mem_curve_iff {t : ℝ} (ht : t ∈ I) : d.cross t ∈ C ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    refine inside_subset_compl (d.cross_inside ⟨⟨t, ht, rfl⟩, ?_⟩) hmem
    rintro (h | h)
    · exact hcon.1 (d.injOn_cross ht zero_mem_I (h.trans d.cross_zero.symm))
    · exact hcon.2 (d.injOn_cross ht one_mem_I (h.trans d.cross_one.symm))
  · rintro (rfl | rfl)
    · rw [d.cross_zero]; exact d.a_mem
    · rw [d.cross_one]; exact d.b_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.cross_mem_curve_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.cross_mem_curve_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.cross_mem_curve_iff ``Submission.Schoenflies.InitialData.cross_mem_curve_iff

theorem crossSet_inter_curve : d.crossSet ∩ C = ({d.a, d.b} : Set Plane) := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨⟨t, ht, rfl⟩, hz⟩
    rcases (d.cross_mem_curve_iff ht).1 hz with rfl | rfl
    exacts [Or.inl d.cross_zero, Or.inr d.cross_one]
  · rintro z (rfl | rfl)
    · exact ⟨⟨0, zero_mem_I, d.cross_zero⟩, d.a_mem⟩
    · exact ⟨⟨1, one_mem_I, d.cross_one⟩, d.b_mem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.crossSet_inter_curve then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.crossSet_inter_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.crossSet_inter_curve ``Submission.Schoenflies.InitialData.crossSet_inter_curve

/-! #### The map -/

open _root_.Classical in
/-- The skeleton map: `u` on the curve, and the parameter-matching homeomorphism from the
crosscut onto the straight chord. -/
noncomputable def skelMap (d : InitialData C) : Plane → Plane :=
  fun x => if x ∈ C then d.u x else tgtChord d.xa d.xb (Function.invFunOn d.cross I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelMap then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelMap ``Submission.Schoenflies.InitialData.skelMap

open _root_.Classical in
/-- Its inverse: `w` on the model curve, and the parameter-matching homeomorphism back. -/
noncomputable def skelInv (d : InitialData C) : Plane → Plane :=
  fun y => if y ∈ modelCurve then d.w y else
    d.cross (Function.invFunOn (tgtChord d.xa d.xb) I y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelInv then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelInv"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelInv ``Submission.Schoenflies.InitialData.skelInv

theorem skelMap_of_mem {x : Plane} (hx : x ∈ C) : d.skelMap x = d.u x := by
  simp only [skelMap, if_pos hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelMap_of_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelMap_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelMap_of_mem ``Submission.Schoenflies.InitialData.skelMap_of_mem

theorem skelInv_of_mem {y : Plane} (hy : y ∈ modelCurve) : d.skelInv y = d.w y := by
  simp only [skelInv, if_pos hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelInv_of_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelInv_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelInv_of_mem ``Submission.Schoenflies.InitialData.skelInv_of_mem

/-- **The skeleton map matches parameters on the crosscut.** -/
theorem skelMap_cross {t : ℝ} (ht : t ∈ I) :
    d.skelMap (d.cross t) = tgtChord d.xa d.xb t := by
  by_cases hmem : d.cross t ∈ C
  · rcases (d.cross_mem_curve_iff ht).1 hmem with rfl | rfl
    · rw [d.skelMap_of_mem hmem, d.cross_zero, d.u_a]
      simp [tgtChord]
    · rw [d.skelMap_of_mem hmem, d.cross_one, d.u_b]
      simp [tgtChord]
  · simp only [skelMap, if_neg hmem, d.injOn_cross.leftInvOn_invFunOn ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelMap_cross then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelMap_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelMap_cross ``Submission.Schoenflies.InitialData.skelMap_cross

theorem tgtChord_mem_modelCurve_iff {t : ℝ} (ht : t ∈ I) :
    tgtChord d.xa d.xb t ∈ modelCurve ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    refine openSegment_chord_notMem_modelCurve d.abs_xa d.abs_xb _ ?_ hmem
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hcon.1), lt_of_le_of_ne ht.2 hcon.2⟩, rfl⟩
  · rintro (rfl | rfl)
    · simp only [tgtChord, AffineMap.lineMap_apply_zero]
      exact tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1
    · simp only [tgtChord, AffineMap.lineMap_apply_one]
      exact tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.tgtChord_mem_modelCurve_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.tgtChord_mem_modelCurve_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.tgtChord_mem_modelCurve_iff ``Submission.Schoenflies.InitialData.tgtChord_mem_modelCurve_iff

theorem injOn_tgtChord : _root_.Set.InjOn (tgtChord d.xa d.xb) I :=
  d.tgt.injOn_chord

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.injOn_tgtChord then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.injOn_tgtChord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.injOn_tgtChord ``Submission.Schoenflies.InitialData.injOn_tgtChord

theorem skelInv_tgtChord {t : ℝ} (ht : t ∈ I) :
    d.skelInv (tgtChord d.xa d.xb t) = d.cross t := by
  by_cases hmem : tgtChord d.xa d.xb t ∈ modelCurve
  · rcases (d.tgtChord_mem_modelCurve_iff ht).1 hmem with rfl | rfl
    · rw [d.skelInv_of_mem hmem, d.cross_zero]
      simp [tgtChord]
    · rw [d.skelInv_of_mem hmem, d.cross_one]
      simp [tgtChord]
  · simp only [skelInv, if_neg hmem, d.injOn_tgtChord.leftInvOn_invFunOn ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skelInv_tgtChord then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skelInv_tgtChord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skelInv_tgtChord ``Submission.Schoenflies.InitialData.skelInv_tgtChord

/-! #### Continuity and inversion -/

theorem continuousOn_skelMap : ContinuousOn d.skelMap d.sourceRealization.skeletonSet := by
  rw [d.sourceRealization_skeletonSet]
  refine Plane.continuousOn_union_of_isClosed d.curve.isClosed ?_ ?_ ?_
  · exact (isCompact_I.image_of_continuousOn d.continuousOn_cross).isClosed
  · exact d.homeo.continuousOn.congr fun x hx => d.skelMap_of_mem hx
  · refine ContinuousOn.congr (f := fun x => tgtChord d.xa d.xb
      (Function.invFunOn d.cross I x)) ?_ ?_
    · refine AffineMap.lineMap_continuous.continuousOn.comp
        (continuousOn_invFunOn_image isCompact_I d.continuousOn_cross d.injOn_cross)
        fun x hx => Function.invFunOn_mem (by rcases hx with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
    · rintro x ⟨t, ht, rfl⟩
      simp only [d.skelMap_cross ht, d.injOn_cross.leftInvOn_invFunOn ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.continuousOn_skelMap then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.continuousOn_skelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.continuousOn_skelMap ``Submission.Schoenflies.InitialData.continuousOn_skelMap

theorem continuousOn_skelInv : ContinuousOn d.skelInv d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet]
  refine Plane.continuousOn_union_of_isClosed isCompact_modelCurve.isClosed ?_ ?_ ?_
  · rw [d.tgt_chordSet]
    exact (isCompact_segment _ _).isClosed
  · exact d.homeo.continuousOn_inv.congr fun y hy => d.skelInv_of_mem hy
  · rw [d.tgt_chordSet, ← tgtChord_image]
    refine ContinuousOn.congr (f := fun y => d.cross (Function.invFunOn (tgtChord d.xa d.xb) I y))
      ?_ ?_
    · refine d.continuousOn_cross.comp
        (continuousOn_invFunOn_image isCompact_I AffineMap.lineMap_continuous.continuousOn
          d.injOn_tgtChord)
        fun y hy => Function.invFunOn_mem (by rcases hy with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
    · rintro y ⟨t, ht, rfl⟩
      simp only [d.skelInv_tgtChord ht, d.injOn_tgtChord.leftInvOn_invFunOn ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.continuousOn_skelInv then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.continuousOn_skelInv"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.continuousOn_skelInv ``Submission.Schoenflies.InitialData.continuousOn_skelInv

theorem leftInvOn_skel :
    LeftInvOn d.skelInv d.skelMap d.sourceRealization.skeletonSet := by
  rw [d.sourceRealization_skeletonSet]
  rintro x (hx | ⟨t, ht, rfl⟩)
  · rw [d.skelMap_of_mem hx, d.skelInv_of_mem (d.homeo.mapsTo hx), d.homeo.leftInvOn hx]
  · rw [d.skelMap_cross ht, d.skelInv_tgtChord ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.leftInvOn_skel then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.leftInvOn_skel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.leftInvOn_skel ``Submission.Schoenflies.InitialData.leftInvOn_skel

theorem rightInvOn_skel :
    RightInvOn d.skelInv d.skelMap d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet, d.tgt_chordSet, ← tgtChord_image]
  rintro y (hy | ⟨t, ht, rfl⟩)
  · rw [d.skelInv_of_mem hy, d.skelMap_of_mem (d.homeo.mapsTo_inv hy), d.homeo.rightInvOn hy]
  · rw [d.skelInv_tgtChord ht, d.skelMap_cross ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.rightInvOn_skel then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.rightInvOn_skel"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.rightInvOn_skel ``Submission.Schoenflies.InitialData.rightInvOn_skel


/-- **The skeleton homeomorphism `g` of `def:matched-pair`.** It is `u` on the outer cycle
(clause 2), and on the crosscut it is the chosen homeomorphism `P → [u(a), u(b)]` matching
endpoints (clause 3); clause 1 is definitional here, both realizations being realizations of
the one `initialStructure`. -/
noncomputable def skeletonHomeo :
    CellStructure.SkeletonHomeo d.sourceRealization d.targetRealization where
  toFun := d.skelMap
  invFun := d.skelInv
  continuousOn_toFun := d.continuousOn_skelMap
  continuousOn_invFun := d.continuousOn_skelInv
  leftInvOn := d.leftInvOn_skel
  rightInvOn := d.rightInvOn_skel
  pos_apply := by
    rintro _ ⟨i, rfl⟩
    have hm : tgtPos d.xa d.xb i ∈ modelCurve := tgtPos_mem_modelCurve d.abs_xa d.abs_xb i
    change d.skelMap (d.w (tgtPos d.xa d.xb i)) = tgtPos d.xa d.xb i
    rw [d.skelMap_of_mem (d.homeo.mapsTo_inv hm), d.homeo.rightInvOn hm]
  edgeArc_image := by
    intro e he
    replace he : e ∈ InitialCell.edges := he
    rcases he with ⟨i, rfl⟩ | rfl
    · change d.skelMap '' ((fun t => d.w (tgtOuter d.xa d.xb i t)) '' I) =
        tgtOuter d.xa d.xb i '' I
      rw [← Set.image_comp]
      refine Set.image_congr fun t ht => ?_
      have hm : tgtOuter d.xa d.xb i t ∈ modelCurve :=
        tgtOuter_subset_modelCurve d.abs_xa d.abs_xb i ⟨t, ht, rfl⟩
      change d.skelMap (d.w (tgtOuter d.xa d.xb i t)) = tgtOuter d.xa d.xb i t
      rw [d.skelMap_of_mem (d.homeo.mapsTo_inv hm), d.homeo.rightInvOn hm]
    · change d.skelMap '' (d.cross '' I) = tgtChord d.xa d.xb '' I
      rw [← Set.image_comp]
      exact Set.image_congr fun t ht => d.skelMap_cross ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skeletonHomeo then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skeletonHomeo"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skeletonHomeo ``Submission.Schoenflies.InitialData.skeletonHomeo

@[simp] theorem skeletonHomeo_toFun : d.skeletonHomeo.toFun = d.skelMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skeletonHomeo_toFun then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skeletonHomeo_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skeletonHomeo_toFun ``Submission.Schoenflies.InitialData.skeletonHomeo_toFun

/-- **Clause 2 of `def:matched-pair`: `g = u` on `C`.** -/
theorem skeletonHomeo_eq_u {x : Plane} (hx : x ∈ C) : d.skeletonHomeo.toFun x = d.u x :=
  d.skelMap_of_mem hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skeletonHomeo_eq_u then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skeletonHomeo_eq_u"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skeletonHomeo_eq_u ``Submission.Schoenflies.InitialData.skeletonHomeo_eq_u

/-- **Clause 3 of `def:matched-pair` for the crosscut**: the chosen homeomorphism
`P → [u(a), u(b)]` matches the two parametrizations, hence the endpoints. -/
theorem skeletonHomeo_cross {t : ℝ} (ht : t ∈ I) :
    d.skeletonHomeo.toFun (d.cross t) = tgtChord d.xa d.xb t := d.skelMap_cross ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.skeletonHomeo_cross then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.skeletonHomeo_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.skeletonHomeo_cross ``Submission.Schoenflies.InitialData.skeletonHomeo_cross


/-! ### The two 2-cells really are the two sides of the crosscut

`thm:general-crosscut` applied on each side. On the source side the collar hypothesis
`HasArcCollars (inside C) P` is carried, since `P` is an arbitrary polygonal crosscut; on the
target side the chord is straight, so `Schoenflies.hasArcCollars_segment` discharges it
outright. -/

/-- **`P` is a crosscut of `D`** — the configuration `thm:general-crosscut` consumes. -/
theorem isCrosscut : IsCrosscut C d.crossSet d.a d.b where
  curve := d.curve
  arc := d.src.isArcBetween_chordSet
  polygonal := d.polygonal_cross
  left_mem := d.a_mem
  right_mem := d.b_mem
  sdiff_subset := d.cross_inside

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isCrosscut then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isCrosscut"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isCrosscut ``Submission.Schoenflies.InitialData.isCrosscut

/-- **`A₁, A₂` are the two arcs of `C` from `a` to `b`.** They are the geometric unions of the
two boundary edge-paths `B₁, B₂` of the abstract structure. -/
theorem isCutPair : IsCutPair C d.a d.b (d.src.arcOf _root_.Bool.false) (d.src.arcOf _root_.Bool.true) where
  fst := d.src.arcOf_false_isArcBetween
  snd := d.src.arcOf_true_isArcBetween.reverse
  union_eq := by rw [d.src.arcOf_union, d.src_outerArcs]
  inter_eq := d.src.arcOf_inter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isCutPair then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isCutPair"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isCutPair ``Submission.Schoenflies.InitialData.isCutPair

theorem sourceRealization_cell_face (k : Bool) :
    d.sourceRealization.cell (.face k) = inside (d.src.arcOf k ∪ d.crossSet) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.sourceRealization_cell_face then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.sourceRealization_cell_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.sourceRealization_cell_face ``Submission.Schoenflies.InitialData.sourceRealization_cell_face

/-- **The two source 2-cells exhaust `D ∖ P`** — `thm:general-crosscut`, first sentence. -/
theorem source_cells_cover (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hcollars : HasArcCollars (inside C) d.crossSet) :
    inside C \ d.crossSet =
      d.sourceRealization.cell (.face _root_.Bool.false) ∪ d.sourceRealization.cell (.face _root_.Bool.true) :=
  d.isCrosscut.inside_diff_eq (fun _ h => h.isSeparating harc) d.isCutPair hcollars

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.source_cells_cover then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.source_cells_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.source_cells_cover ``Submission.Schoenflies.InitialData.source_cells_cover

/-- **Each source 2-cell is a component of `D ∖ P`.** -/
theorem source_cell_isComponent (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (k : Bool) : ∀ z ∈ d.sourceRealization.cell (.face k),
      connectedComponentIn (inside C \ d.crossSet) z = d.sourceRealization.cell (.face k) := by
  cases k
  · exact d.isCrosscut.side_isComponent (fun _ h => h.isSeparating harc) d.isCutPair
  · exact d.isCrosscut.side_isComponent (fun _ h => h.isSeparating harc) d.isCutPair.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.source_cell_isComponent then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.source_cell_isComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.source_cell_isComponent ``Submission.Schoenflies.InitialData.source_cell_isComponent

/-- **The labelling of the two source 2-cells**: the closure of `Rₖ` meets `C` exactly in
`Aₖ`. This is what makes `k ↦ face k` the correspondence `lem:crosscut-side-correspondence`
asks for. -/
theorem source_closure_cell_inter (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (k : Bool) : closure (d.sourceRealization.cell (.face k)) ∩ C = d.src.arcOf k := by
  cases k
  · exact d.isCrosscut.closure_side_inter (fun _ h => h.isSeparating harc) d.isCutPair
  · exact d.isCrosscut.closure_side_inter (fun _ h => h.isSeparating harc) d.isCutPair.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.source_closure_cell_inter then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.source_closure_cell_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.source_closure_cell_inter ``Submission.Schoenflies.InitialData.source_closure_cell_inter

theorem source_cells_ne (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ) :
    d.sourceRealization.cell (.face _root_.Bool.false) ≠ d.sourceRealization.cell (.face _root_.Bool.true) :=
  d.isCrosscut.side_ne (fun _ h => h.isSeparating harc) d.isCutPair

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.source_cells_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.source_cells_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.source_cells_ne ``Submission.Schoenflies.InitialData.source_cells_ne

/-! #### The target side -/

/-- The open square is the bounded region of the model curve: it is open, convex and bounded,
and its frontier is contained in `S`. -/
theorem openSquare_subset_inside_modelCurve : Plane.openSquare 0 1 ⊆ inside modelCurve := by
  have hbdd : Bornology.IsBounded (Plane.openSquare 0 1) := by
    refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2)).subset fun x hx => ?_
    have hx1 : Plane.supNorm x < 1 := mem_openSquare_zero_one.1 hx
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have := Plane.norm_le_sqrt_two_mul_supNorm x
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [Plane.supNorm_nonneg x]
  have hsub : Plane.openSquare 0 1 ⊆ modelCurveᶜ := fun x hx hxm =>
    absurd (mem_openSquare_zero_one.1 hx) (by rw [show Plane.supNorm x = 1 from hxm]; norm_num)
  have hfr : frontier (Plane.openSquare 0 1) ∩ modelCurveᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hz'⟩
    refine hz' ?_
    have hzc : z ∈ Plane.closedSquare 0 1 :=
      (Plane.isClosed_closedSquare 0 1).closure_subset
        (closure_mono (fun x hx => mem_closedSquare_zero_one.2
          (mem_openSquare_zero_one.1 hx).le) hz.1)
    have hzo : z ∉ Plane.openSquare 0 1 := by
      rw [(Plane.isOpen_openSquare 0 1).frontier_eq] at hz
      exact hz.2
    exact le_antisymm (mem_closedSquare_zero_one.1 hzc)
      (not_lt.1 fun h => hzo (mem_openSquare_zero_one.2 h))
  intro z hz
  refine ⟨hsub hz, ?_⟩
  rw [Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare 0 1)
    (Plane.convex_openSquare 0 1).isPreconnected hsub hfr hz]
  exact hbdd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.openSquare_subset_inside_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.openSquare_subset_inside_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.openSquare_subset_inside_modelCurve ``Submission.Schoenflies.InitialData.openSquare_subset_inside_modelCurve

/-- **The straight chord is a crosscut of the open square.** -/
theorem isCrosscutTarget :
    IsCrosscut modelCurve (d.tgt.chordSet) (Plane.mk d.xa 1) (Plane.mk d.xb (-1)) where
  curve := isJordanCurve_modelCurve
  arc := d.tgt.isArcBetween_chordSet
  polygonal := by rw [d.tgt_chordSet]; exact isPolygonal_segment _ _
  left_mem := tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1
  right_mem := tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4
  sdiff_subset := by
    rw [d.tgt_chordSet]
    rintro z ⟨hz, hzne⟩
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact absurd (Or.inl rfl) hzne
    · exact absurd (Or.inr rfl) hzne
    · exact openSquare_subset_inside_modelCurve (mem_openSquare_zero_one.2
        (openSegment_chord_supNorm_lt d.abs_xa d.abs_xb _ hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isCrosscutTarget then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isCrosscutTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isCrosscutTarget ``Submission.Schoenflies.InitialData.isCrosscutTarget

/-- **`u(A₁), u(A₂)` are the two arcs of `S` from `u(a)` to `u(b)`.** -/
theorem isCutPairTarget :
    IsCutPair modelCurve (Plane.mk d.xa 1) (Plane.mk d.xb (-1))
      (d.tgt.arcOf _root_.Bool.false) (d.tgt.arcOf _root_.Bool.true) where
  fst := d.tgt.arcOf_false_isArcBetween
  snd := d.tgt.arcOf_true_isArcBetween.reverse
  union_eq := by rw [d.tgt.arcOf_union, d.tgt_outerArcs]
  inter_eq := d.tgt.arcOf_inter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.isCutPairTarget then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.isCutPairTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.isCutPairTarget ``Submission.Schoenflies.InitialData.isCutPairTarget

/-- The collar hypothesis is not needed on the target side: the chord is a segment. -/
theorem hasArcCollarsTarget : HasArcCollars (inside modelCurve) d.tgt.chordSet := by
  rw [d.tgt_chordSet]
  refine hasArcCollars_segment ?_ (isOpen_inside isJordanCurve_modelCurve.isClosed) ?_ ?_ ?_
  · intro h
    have := (Plane.mk_inj h).2
    norm_num at this
  · exact fun h => inside_subset_compl h (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)
  · exact fun h => inside_subset_compl h (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)
  · rw [← d.tgt_chordSet]; exact d.isCrosscutTarget.sdiff_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.hasArcCollarsTarget then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.hasArcCollarsTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.hasArcCollarsTarget ``Submission.Schoenflies.InitialData.hasArcCollarsTarget

theorem targetRealization_cell_face (k : Bool) :
    d.targetRealization.cell (.face k) = inside (d.tgt.arcOf k ∪ d.tgt.chordSet) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.targetRealization_cell_face then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.targetRealization_cell_face"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.targetRealization_cell_face ``Submission.Schoenflies.InitialData.targetRealization_cell_face

/-- **The two target 2-cells exhaust `Q° ∖ [u(a), u(b)]`.** -/
theorem target_cells_cover (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ) :
    inside modelCurve \ d.tgt.chordSet =
      d.targetRealization.cell (.face _root_.Bool.false) ∪ d.targetRealization.cell (.face _root_.Bool.true) :=
  d.isCrosscutTarget.inside_diff_eq (fun _ h => h.isSeparating harc) d.isCutPairTarget
    d.hasArcCollarsTarget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.target_cells_cover then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.target_cells_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.target_cells_cover ``Submission.Schoenflies.InitialData.target_cells_cover

/-- **The labelling of the two target 2-cells.** -/
theorem target_closure_cell_inter (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (k : Bool) :
    closure (d.targetRealization.cell (.face k)) ∩ modelCurve = d.tgt.arcOf k := by
  cases k
  · exact d.isCrosscutTarget.closure_side_inter (fun _ h => h.isSeparating harc) d.isCutPairTarget
  · exact d.isCrosscutTarget.closure_side_inter (fun _ h => h.isSeparating harc)
      d.isCutPairTarget.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.InitialData.target_closure_cell_inter then
    throwError "Refusing to shadow existing declaration Schoenflies.InitialData.target_closure_cell_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.InitialData.target_closure_cell_inter ``Submission.Schoenflies.InitialData.target_closure_cell_inter


end InitialData

/-! ### `prop:initial-pair`: an initial matched pair exists

The two open corner arcs the blueprint chooses `a` and `b` from are the relative interiors of
two *opposite* sides of the square, pulled back by `u`. They are relatively open in `C` and
nonempty, so the countable dense set of strongly accessible points of
`prop:countable-strong-access` meets both; `lem:tangent-cone` and `lem:accessible-endpoints`
then supply the polygonal crosscut. -/

/-- The relative interior of the top side of the square. -/
def openTop : Set Plane := {p : Plane | |p 0| < 1 ∧ 0 < p 1} ∩ modelCurve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openTop then
    throwError "Refusing to shadow existing declaration Schoenflies.openTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openTop ``Submission.Schoenflies.openTop

/-- The relative interior of the bottom side — the side *opposite* the top one. -/
def openBottom : Set Plane := {p : Plane | |p 0| < 1 ∧ p 1 < 0} ∩ modelCurve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openBottom then
    throwError "Refusing to shadow existing declaration Schoenflies.openBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openBottom ``Submission.Schoenflies.openBottom

theorem isOpen_topBand : IsOpen {p : Plane | |p 0| < 1 ∧ 0 < p 1} := by
  have h1 : IsOpen {p : Plane | |p 0| < 1} :=
    isOpen_lt (continuous_abs.comp (Plane.continuous_coord 0)) continuous_const
  have h2 : IsOpen {p : Plane | 0 < p 1} := isOpen_lt continuous_const (Plane.continuous_coord 1)
  exact h1.inter h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isOpen_topBand then
    throwError "Refusing to shadow existing declaration Schoenflies.isOpen_topBand"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isOpen_topBand ``Submission.Schoenflies.isOpen_topBand

theorem isOpen_bottomBand : IsOpen {p : Plane | |p 0| < 1 ∧ p 1 < 0} := by
  have h1 : IsOpen {p : Plane | |p 0| < 1} :=
    isOpen_lt (continuous_abs.comp (Plane.continuous_coord 0)) continuous_const
  have h2 : IsOpen {p : Plane | p 1 < 0} := isOpen_lt (Plane.continuous_coord 1) continuous_const
  exact h1.inter h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isOpen_bottomBand then
    throwError "Refusing to shadow existing declaration Schoenflies.isOpen_bottomBand"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isOpen_bottomBand ``Submission.Schoenflies.isOpen_bottomBand

theorem mem_openTop {p : Plane} : p ∈ openTop ↔ p 1 = 1 ∧ |p 0| < 1 := by
  constructor
  · rintro ⟨⟨h0, hpos⟩, hm⟩
    have hmax : _root_.Max.max |p 0| |p 1| = 1 := hm
    refine ⟨?_, h0⟩
    rcases max_choice |p 0| |p 1| with h | h
    · exact absurd (h ▸ hmax) (ne_of_lt h0)
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 (h ▸ hmax) with h' | h'
      · exact h'
      · linarith
  · rintro ⟨h1, h0⟩
    refine ⟨⟨h0, by rw [h1]; norm_num⟩, ?_⟩
    change _root_.Max.max |p 0| |p 1| = 1
    rw [h1, show |(1:ℝ)| = 1 by norm_num]
    exact max_eq_right h0.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_openTop then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_openTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_openTop ``Submission.Schoenflies.mem_openTop

theorem mem_openBottom {p : Plane} : p ∈ openBottom ↔ p 1 = -1 ∧ |p 0| < 1 := by
  constructor
  · rintro ⟨⟨h0, hneg⟩, hm⟩
    have hmax : _root_.Max.max |p 0| |p 1| = 1 := hm
    refine ⟨?_, h0⟩
    rcases max_choice |p 0| |p 1| with h | h
    · exact absurd (h ▸ hmax) (ne_of_lt h0)
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 (h ▸ hmax) with h' | h'
      · linarith
      · exact h'
  · rintro ⟨h1, h0⟩
    refine ⟨⟨h0, by rw [h1]; norm_num⟩, ?_⟩
    change _root_.Max.max |p 0| |p 1| = 1
    rw [h1, show |(-1:ℝ)| = 1 by norm_num]
    exact max_eq_right h0.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_openBottom then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_openBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_openBottom ``Submission.Schoenflies.mem_openBottom

theorem openTop_nonempty : (openTop).Nonempty :=
  ⟨Plane.mk 0 1, mem_openTop.2 ⟨rfl, by norm_num⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openTop_nonempty then
    throwError "Refusing to shadow existing declaration Schoenflies.openTop_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openTop_nonempty ``Submission.Schoenflies.openTop_nonempty

theorem openBottom_nonempty : (openBottom).Nonempty :=
  ⟨Plane.mk 0 (-1), mem_openBottom.2 ⟨rfl, by norm_num⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.openBottom_nonempty then
    throwError "Refusing to shadow existing declaration Schoenflies.openBottom_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.openBottom_nonempty ``Submission.Schoenflies.openBottom_nonempty

/-- A dense subset of `C` meets every nonempty relatively open subset of `C`. -/
theorem exists_mem_inter_of_dense {C A U W : Set Plane} (hAC : A ⊆ C) (hdense : C ⊆ closure A)
    (hW : IsOpen W) (hU : U = W ∩ C) (hne : U.Nonempty) : (A ∩ U).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  have hzC : z ∈ C := (hU ▸ hz).2
  have hzW : z ∈ W := (hU ▸ hz).1
  obtain ⟨y, hyW, hyA⟩ := _root_.mem_closure_iff.1 (hdense hzC) W hW hzW
  exact ⟨y, hyA, hU ▸ ⟨hyW, hAC hyA⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.exists_mem_inter_of_dense then
    throwError "Refusing to shadow existing declaration Schoenflies.exists_mem_inter_of_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.exists_mem_inter_of_dense ``Submission.Schoenflies.exists_mem_inter_of_dense

variable {C : Set Plane}

/-- **`prop:initial-pair`.** Every Jordan curve carries an initial matched pair: a common
abstract cell structure with an admissible realization in `C ∪ D` — `C` subdivided at the
`u`-preimages of the four corners and at two strongly accessible points `a, b` of nonadjacent
corner arcs, together with a polygonal crosscut of `D` from `a` to `b` — and an admissible
realization in `Q`, namely `S` correspondingly subdivided together with the straight chord
`[u(a), u(b)]`.

`harc` is `thm:arc-complement`, the standing hypothesis of `thm:jordan` in this library. -/
theorem exists_initialData (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) : Nonempty (InitialData C) := by
  have hsep : IsSeparating C := hC.isSeparating harc
  obtain ⟨u, w, hhom⟩ := exists_isSetHomeoOn_modelCurve hC
  -- the countable dense set of strongly accessible points
  have hDmax : ∀ q ∈ inside C, connectedComponentIn Cᶜ q ⊆ inside C := by
    intro q hq z hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hq.2
  have hCD : C ⊆ closure (inside C) := by
    intro x hx
    have hxf : x ∈ frontier (inside C) := by rw [hsep.frontier_inside]; exact hx
    exact hxf.1
  obtain ⟨A, hAC, -, hAacc, hCA⟩ := exists_countable_dense_stronglyAccessible hC.isCompact
    hC.nonempty hsep.isOpen_inside inside_subset_compl hDmax hCD
  -- the two open corner arcs, relatively open in `C` and nonempty
  obtain ⟨W₁, hW₁, hW₁eq⟩ := hhom.symm.image_isRelOpen isOpen_topBand (U := openTop) rfl
  obtain ⟨W₂, hW₂, hW₂eq⟩ := hhom.symm.image_isRelOpen isOpen_bottomBand (U := openBottom) rfl
  obtain ⟨a₀, ha₀A, ha₀⟩ := exists_mem_inter_of_dense hAC hCA hW₁ hW₁eq
    (openTop_nonempty.image w)
  obtain ⟨b₀, hb₀A, hb₀⟩ := exists_mem_inter_of_dense hAC hCA hW₂ hW₂eq
    (openBottom_nonempty.image w)
  obtain ⟨q₁, hq₁, rfl⟩ := ha₀
  obtain ⟨q₂, hq₂, rfl⟩ := hb₀
  have hq₁m : q₁ ∈ modelCurve := hq₁.2
  have hq₂m : q₂ ∈ modelCurve := hq₂.2
  obtain ⟨hq₁1, hq₁0⟩ := mem_openTop.1 hq₁
  obtain ⟨hq₂1, hq₂0⟩ := mem_openBottom.1 hq₂
  set xa : ℝ := q₁ 0 with hxa
  set xb : ℝ := q₂ 0 with hxb
  have hq₁eq : q₁ = tgtPos xa xb 1 := Plane.eq_mk rfl hq₁1
  have hq₂eq : q₂ = tgtPos xa xb 4 := Plane.eq_mk rfl hq₂1
  -- the two chosen boundary points
  have haC : w q₁ ∈ C := hhom.mapsTo_inv hq₁m
  have hbC : w q₂ ∈ C := hhom.mapsTo_inv hq₂m
  have hab : w q₁ ≠ w q₂ := by
    intro h
    have := hhom.rightInvOn hq₁m
    rw [h, hhom.rightInvOn hq₂m] at this
    rw [← this] at hq₁1
    rw [hq₂1] at hq₁1
    norm_num at hq₁1
  -- the polygonal crosscut
  obtain ⟨ws, -, -, -, hwsin, hwsarc, -⟩ := exists_crosscut_of_polyAccessible
    hsep.isOpen_inside hsep.isConnected_inside.isPreconnected
    (Set.disjoint_left.2 fun x hx => inside_subset_compl hx) hab haC hbC
    (hAacc _ ha₀A).polyAccessible (hAacc _ hb₀A).polyAccessible
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hwsarc
  refine ⟨{ u := u, w := w, homeo := hhom, curve := hC, xa := xa, xb := xb
            abs_xa := hq₁0, abs_xb := hq₂0
            cross := f
            continuousOn_cross := hfc, injOn_cross := hfi
            cross_zero := by rw [hf0, hq₁eq]
            cross_one := by rw [hf1, hq₂eq]
            cross_inside := ?_
            polygonal_cross := ?_ }⟩
  · rw [hfim, ← hq₁eq, ← hq₂eq]
    intro z hz
    exact hwsin ⟨hz.1, by simpa [hf0, hf1] using hz.2⟩
  · rw [hfim]
    exact ⟨ws, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.exists_initialData then
    throwError "Refusing to shadow existing declaration Schoenflies.exists_initialData"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.exists_initialData ``Submission.Schoenflies.exists_initialData


/-- **`prop:initial-pair`, assembled.** There is a matched pair whose source realization is `C`
subdivided at the `u`-preimages of the four corners of `Q` and at two further points `a, b` of
the countable dense strongly accessible set lying in two nonadjacent corner arcs, together with
one polygonal crosscut of `D` from `a` to `b`, and whose target realization is `S`
correspondingly subdivided together with the straight chord `[u(a), u(b)]`.

Both realizations realize the one `Schoenflies.initialStructure`, so clause 1 of
`def:matched-pair` is definitional; clause 2 is the last conjunct; clause 3 is
`InitialData.skeletonHomeo` together with `InitialData.skeletonHomeo_cross`. Admissibility
(`def:admissible-graph`) is the first six conjuncts.

Everything here is available separately, as a function of the `InitialData` produced: this
bundle exists so that the blueprint statement appears once, in one place. `def:generated-
structure` builds every later stage from `InitialData.sourceRealization`,
`InitialData.targetRealization` and `InitialData.skeletonHomeo`, and needs them as data, not as
the content of an existential. -/
theorem initial_pair (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ) (hC : IsJordanCurve C) :
    ∃ d : InitialData C,
      (d.sourceRealization.graph).IsTwoConnected ∧
      (d.targetRealization.graph).IsTwoConnected ∧
      d.sourceRealization.outerSet = C ∧
      d.targetRealization.outerSet = modelCurve ∧
      IsConnected d.sourceRealization.nonboundary ∧
      IsConnected d.targetRealization.nonboundary ∧
      IsPolygonal d.crossSet ∧
      d.tgt.chordSet = segment ℝ (d.u d.a) (d.u d.b) ∧
      (∀ x ∈ C, d.skeletonHomeo.toFun x = d.u x) := by
  obtain ⟨d⟩ := exists_initialData harc hC
  exact ⟨d, d.isTwoConnected_sourceRealization, d.isTwoConnected_targetRealization,
    d.sourceRealization_outerSet, d.targetRealization_outerSet,
    d.isConnected_sourceRealization_nonboundary, d.isConnected_targetRealization_nonboundary,
    d.polygonal_cross, by rw [d.tgt_chordSet, d.u_apply_a, d.u_apply_b],
    fun x hx => d.skeletonHomeo_eq_u hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.initial_pair then
    throwError "Refusing to shadow existing declaration Schoenflies.initial_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.initial_pair ``Submission.Schoenflies.initial_pair


end Schoenflies
