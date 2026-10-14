/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Degree and the handshake lemma

Degree counting on Mathlib's multigraph `Graph α β`, for graphs with finitely many vertices
and finitely many edges.

## Carrying finiteness

`V(G)` and `E(G)` are `Set α` and `Set β`, not types, so finiteness has to be carried
somehow. The choice made here — and inherited by every later graph module — is a
`Prop`-valued class

```
class Graph.Finite (G : Graph α β) : Prop
```

bundling `V(G).Finite` and `E(G).Finite`, with `G.vertexFinset` and `G.edgeFinset` derived
from it. The reasons:

* It is a `Prop`, so it is proof irrelevant. `G.vertexFinset` and `G.degree` therefore do not
  depend on *which* finiteness proof is in scope, and two lemmas proved with different
  instances still compose. A bundled `Finset`-valued structure would not have that property:
  it duplicates the `vertexSet` data and forces a `↑G.vertexFinset = V(G)` side condition at
  every call site.
* It is a class, so it is silent at the call site — the statements below read like ordinary
  graph theory instead of dragging two `Set.Finite` hypotheses through every signature. The
  price is that a subgraph does not get an instance for free; `Graph.Finite.of_le` produces
  one, and `haveI` installs it locally. That is the right trade: in this development
  finiteness is a standing assumption on the ambient graph and subgraphs are formed
  constantly.
* `Finite ↥V(G)` and `Finite ↥E(G)` instances are provided too, so Mathlib's own machinery
  (`Set.Finite.subset`, `Set.toFinite`, ...) fires without help.

Counts are `Set.ncard`. `Set.ncard` is total — it is `0` on an infinite set — so `G.degree`
is defined for every graph and needs no instance argument; finiteness enters only where a
theorem actually needs it.

## Degree

`G.degree x` is the number of *edge ends* at `x`:

```
G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard
```

A non-loop edge at `x` is counted once, by the first summand. A loop at `x` is counted
twice, once by each summand. This is the definition the handshake lemma needs, and it agrees
with `SimpleGraph.degree` on loopless graphs.

## Blueprint

* `Graph.sum_degree_eq_two_mul_ncard_edgeSet` — "the degree sum is twice the number of
  edges", the counting step in the proof of Lemma `lem:three-leaf-tree` (Trees with three
  leaves). The whole content is `Graph.ncard_inc_add_ncard_isLoopAt`: an edge has exactly two
  ends.
* `Graph.IsLeaf` — "the vertices of degree one are the leaves", same lemma.

## Namespace

Everything lives in the root `Graph` namespace rather than in `Schoenflies`, so that dot
notation `G.degree`, `G.IsLeaf`, `G.vertexFinset` works on a `G : Graph α β`. Later graph
modules should do the same.
-/

open scoped _root_.Graph

namespace Graph
open _root_.Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-! ### Finiteness -/

open _root_.Graph in
/-- `G.Finite` says that the multigraph `G` has finitely many vertices and finitely many
edges. Both halves are needed: the vertex set does not bound the edge set (parallel edges)
and the edge set does not bound the vertex set (isolated vertices). -/
class Finite (G : Graph α β) : Prop where
  /-- A finite graph has finitely many vertices. -/
  finite_vertexSet : V(G).Finite
  /-- A finite graph has finitely many edges. -/
  finite_edgeSet : E(G).Finite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.Finite then
    throwError "Refusing to shadow existing declaration Graph.Finite"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Finite ``Submission.Graph.Finite

open _root_.Graph in
theorem finite_vertexSet (G : Graph α β) [G.Finite] : V(G).Finite := Finite.finite_vertexSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.finite_vertexSet then
    throwError "Refusing to shadow existing declaration Graph.finite_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.finite_vertexSet ``Submission.Graph.finite_vertexSet

open _root_.Graph in
theorem finite_edgeSet (G : Graph α β) [G.Finite] : E(G).Finite := Finite.finite_edgeSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.finite_edgeSet then
    throwError "Refusing to shadow existing declaration Graph.finite_edgeSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.finite_edgeSet ``Submission.Graph.finite_edgeSet

open _root_.Graph in
instance _root_.Submission.Graph.instFiniteElemVertexSetOfFinite [G.Finite] : _root_.Finite V(G) := Set.finite_coe_iff.2 (finite_vertexSet G)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.instFiniteElemVertexSetOfFinite then
    throwError "Refusing to shadow existing declaration Graph.instFiniteElemVertexSetOfFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.instFiniteElemVertexSetOfFinite ``Submission.Graph.instFiniteElemVertexSetOfFinite

open _root_.Graph in
instance _root_.Submission.Graph.instFiniteElemEdgeSetOfFinite [G.Finite] : _root_.Finite E(G) := Set.finite_coe_iff.2 (finite_edgeSet G)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.instFiniteElemEdgeSetOfFinite then
    throwError "Refusing to shadow existing declaration Graph.instFiniteElemEdgeSetOfFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.instFiniteElemEdgeSetOfFinite ``Submission.Graph.instFiniteElemEdgeSetOfFinite

/-- A subgraph of a finite graph is finite. This is not an instance — `H` cannot be
recovered from the goal — so install it with `haveI := Graph.Finite.of_le h`. -/
theorem Finite.of_le (h : H ≤ G) [G.Finite] : H.Finite :=
  ⟨(_root_.Submission.Graph.finite_vertexSet G).subset h.vertexSet_mono,
   (_root_.Submission.Graph.finite_edgeSet G).subset h.edgeSet_mono⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.Finite
  let env ← Lean.getEnv
  if env.contains `Graph.Finite.of_le then
    throwError "Refusing to shadow existing declaration Graph.Finite.of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.Finite.of_le ``Submission.Graph.Finite.of_le

open _root_.Graph in
/-- The vertex set of a finite graph, as a `Finset`. -/
noncomputable def vertexFinset (G : Graph α β) [G.Finite] : Finset α :=
  (finite_vertexSet G).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.vertexFinset then
    throwError "Refusing to shadow existing declaration Graph.vertexFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.vertexFinset ``Submission.Graph.vertexFinset

open _root_.Graph in
/-- The edge set of a finite graph, as a `Finset`. -/
noncomputable def edgeFinset (G : Graph α β) [G.Finite] : Finset β :=
  (finite_edgeSet G).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.edgeFinset then
    throwError "Refusing to shadow existing declaration Graph.edgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.edgeFinset ``Submission.Graph.edgeFinset

open _root_.Graph in
@[simp]
theorem mem_vertexFinset [G.Finite] : x ∈ G.vertexFinset ↔ x ∈ V(G) :=
  Set.Finite.mem_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_vertexFinset then
    throwError "Refusing to shadow existing declaration Graph.mem_vertexFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_vertexFinset ``Submission.Graph.mem_vertexFinset

open _root_.Graph in
@[simp]
theorem mem_edgeFinset [G.Finite] : e ∈ G.edgeFinset ↔ e ∈ E(G) :=
  Set.Finite.mem_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.mem_edgeFinset then
    throwError "Refusing to shadow existing declaration Graph.mem_edgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.mem_edgeFinset ``Submission.Graph.mem_edgeFinset

open _root_.Graph in
@[simp, norm_cast]
theorem coe_vertexFinset [G.Finite] : (G.vertexFinset : Set α) = V(G) :=
  Set.Finite.coe_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coe_vertexFinset then
    throwError "Refusing to shadow existing declaration Graph.coe_vertexFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coe_vertexFinset ``Submission.Graph.coe_vertexFinset

open _root_.Graph in
@[simp, norm_cast]
theorem coe_edgeFinset [G.Finite] : (G.edgeFinset : Set β) = E(G) :=
  Set.Finite.coe_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.coe_edgeFinset then
    throwError "Refusing to shadow existing declaration Graph.coe_edgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.coe_edgeFinset ``Submission.Graph.coe_edgeFinset

open _root_.Graph in
@[simp]
theorem card_vertexFinset [G.Finite] : G.vertexFinset.card = V(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_vertexFinset]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.card_vertexFinset then
    throwError "Refusing to shadow existing declaration Graph.card_vertexFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.card_vertexFinset ``Submission.Graph.card_vertexFinset

open _root_.Graph in
@[simp]
theorem card_edgeFinset [G.Finite] : G.edgeFinset.card = E(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.card_edgeFinset then
    throwError "Refusing to shadow existing declaration Graph.card_edgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.card_edgeFinset ``Submission.Graph.card_edgeFinset

/-! ### Incidence sets, unfolded -/

open _root_.Graph in
theorem incidenceSet_eq_setOf (G : Graph α β) (x : α) : G.incidenceSet x = {e | G.Inc e x} :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.incidenceSet_eq_setOf then
    throwError "Refusing to shadow existing declaration Graph.incidenceSet_eq_setOf"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.incidenceSet_eq_setOf ``Submission.Graph.incidenceSet_eq_setOf

open _root_.Graph in
theorem loopSet_eq_setOf (G : Graph α β) (x : α) : G.loopSet x = {e | G.IsLoopAt e x} :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.loopSet_eq_setOf then
    throwError "Refusing to shadow existing declaration Graph.loopSet_eq_setOf"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.loopSet_eq_setOf ``Submission.Graph.loopSet_eq_setOf

open _root_.Graph in
theorem finite_incidenceSet [G.Finite] (x : α) : (G.incidenceSet x).Finite :=
  (finite_edgeSet G).subset (G.incidenceSet_subset_edgeSet x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.finite_incidenceSet then
    throwError "Refusing to shadow existing declaration Graph.finite_incidenceSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.finite_incidenceSet ``Submission.Graph.finite_incidenceSet

open _root_.Graph in
theorem finite_loopSet [G.Finite] (x : α) : (G.loopSet x).Finite :=
  (finite_incidenceSet x).subset (G.loopSet_subset_incidenceSet x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.finite_loopSet then
    throwError "Refusing to shadow existing declaration Graph.finite_loopSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.finite_loopSet ``Submission.Graph.finite_loopSet

/-! ### Degree -/

open _root_.Graph in
/-- `G.degree x` is the number of edge ends of `G` at the vertex `x`: a non-loop edge
incident with `x` contributes one, a loop at `x` contributes two. -/
noncomputable def degree (G : Graph α β) (x : α) : ℕ :=
  (G.incidenceSet x).ncard + (G.loopSet x).ncard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree then
    throwError "Refusing to shadow existing declaration Graph.degree"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree ``Submission.Graph.degree

open _root_.Graph in
theorem degree_def (G : Graph α β) (x : α) :
    G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree_def then
    throwError "Refusing to shadow existing declaration Graph.degree_def"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree_def ``Submission.Graph.degree_def

open _root_.Graph in
/-- A vertex outside the graph has no edge ends. -/
@[simp]
theorem degree_eq_zero_of_notMem (h : x ∉ V(G)) : G.degree x = 0 := by
  have h1 : G.incidenceSet x = ∅ := by
    ext e
    simp only [_root_.Graph.mem_incidenceSet, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h hx.vertex_mem
  have h2 : G.loopSet x = ∅ :=
    Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
  rw [degree_def, h1, h2]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree_eq_zero_of_notMem then
    throwError "Refusing to shadow existing declaration Graph.degree_eq_zero_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree_eq_zero_of_notMem ``Submission.Graph.degree_eq_zero_of_notMem

open _root_.Graph in
/-- Loops are counted among the incident edges as well, so they never make the loop term the
larger of the two. -/
theorem ncard_loopSet_le_ncard_incidenceSet [G.Finite] (x : α) :
    (G.loopSet x).ncard ≤ (G.incidenceSet x).ncard :=
  Set.ncard_le_ncard (G.loopSet_subset_incidenceSet x) (finite_incidenceSet x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.ncard_loopSet_le_ncard_incidenceSet then
    throwError "Refusing to shadow existing declaration Graph.ncard_loopSet_le_ncard_incidenceSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.ncard_loopSet_le_ncard_incidenceSet ``Submission.Graph.ncard_loopSet_le_ncard_incidenceSet

open _root_.Graph in
theorem ncard_incidenceSet_le_degree (x : α) : (G.incidenceSet x).ncard ≤ G.degree x :=
  Nat.le_add_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.ncard_incidenceSet_le_degree then
    throwError "Refusing to shadow existing declaration Graph.ncard_incidenceSet_le_degree"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.ncard_incidenceSet_le_degree ``Submission.Graph.ncard_incidenceSet_le_degree

open _root_.Graph in
/-- On a loopless vertex the degree is just the number of incident edges. -/
theorem degree_eq_ncard_incidenceSet (h : ∀ e, ¬ G.IsLoopAt e x) :
    G.degree x = (G.incidenceSet x).ncard := by
  have : G.loopSet x = ∅ := by
    ext e
    simpa using h e
  rw [degree_def, this]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree_eq_ncard_incidenceSet then
    throwError "Refusing to shadow existing declaration Graph.degree_eq_ncard_incidenceSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree_eq_ncard_incidenceSet ``Submission.Graph.degree_eq_ncard_incidenceSet

open _root_.Graph _root_.Graph.IsLoopAt in
/-- A loop at `x` contributes two to the degree of `x`. -/
theorem IsLoopAt.two_le_degree [G.Finite] (h : G.IsLoopAt e x) : 2 ≤ G.degree x := by
  have h1 : 1 ≤ (G.loopSet x).ncard :=
    (Set.ncard_pos (finite_loopSet x)).2 ⟨e, h⟩
  have h2 : 1 ≤ (G.incidenceSet x).ncard :=
    (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h.inc⟩
  rw [degree_def]
  omega

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.IsLoopAt
  let env ← Lean.getEnv
  if env.contains `Graph.IsLoopAt.two_le_degree then
    throwError "Refusing to shadow existing declaration Graph.IsLoopAt.two_le_degree"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLoopAt.two_le_degree ``Submission.Graph.IsLoopAt.two_le_degree

open _root_.Graph in
theorem degree_pos_of_inc [G.Finite] (h : G.Inc e x) : 0 < G.degree x := by
  have : 0 < (G.incidenceSet x).ncard := (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h⟩
  rw [degree_def]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree_pos_of_inc then
    throwError "Refusing to shadow existing declaration Graph.degree_pos_of_inc"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree_pos_of_inc ``Submission.Graph.degree_pos_of_inc

open _root_.Graph in
theorem degree_eq_zero_iff [G.Finite] : G.degree x = 0 ↔ ∀ e, ¬ G.Inc e x := by
  refine ⟨fun h e he => ?_, fun h => ?_⟩
  · exact absurd h (degree_pos_of_inc he).ne'
  · have h1 : G.incidenceSet x = ∅ := by
      ext e
      simpa using h e
    have h2 : G.loopSet x = ∅ :=
      Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
    rw [degree_def, h1, h2]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.degree_eq_zero_iff then
    throwError "Refusing to shadow existing declaration Graph.degree_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.degree_eq_zero_iff ``Submission.Graph.degree_eq_zero_iff

/-! ### An edge has exactly two ends

This is the entire content of the handshake lemma: summed over the vertices, the number of
ends an edge has there is two, whether the edge is a loop (two ends at one vertex) or not
(one end at each of two vertices).
-/

open _root_.Graph in
/-- An edge of `G` has exactly two ends: the vertices it is incident with, counted again at
the vertex it is a loop at, total two. -/
theorem ncard_inc_add_ncard_isLoopAt (G : Graph α β) (he : e ∈ E(G)) :
    {x | G.Inc e x}.ncard + {x | G.IsLoopAt e x}.ncard = 2 := by
  obtain ⟨u, v, huv⟩ := _root_.Graph.exists_isLink_of_mem_edgeSet he
  by_cases huv' : u = v
  · -- A loop: one vertex, counted by both summands.
    subst huv'
    have hl : G.IsLoopAt e u := huv
    have h1 : {x | G.Inc e x} = {u} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h).symm, fun h => h ▸ hl.inc⟩
    have h2 : {x | G.IsLoopAt e x} = {u} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h.inc).symm, fun h => h ▸ hl⟩
    rw [h1, h2]
    simp
  · -- A non-loop: two distinct vertices, one end at each, and no loop anywhere.
    have h1 : {x | G.Inc e x} = {u, v} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.eq_or_eq_of_isLink huv,
        fun h => h.elim (fun hz => hz ▸ huv.inc_left) (fun hz => hz ▸ huv.inc_right)⟩
    have h2 : {x | G.IsLoopAt e x} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact huv' ((hz.eq_of_inc huv.inc_left).symm.trans (hz.eq_of_inc huv.inc_right))
    rw [h1, h2, Set.ncard_pair huv']
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.ncard_inc_add_ncard_isLoopAt then
    throwError "Refusing to shadow existing declaration Graph.ncard_inc_add_ncard_isLoopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.ncard_inc_add_ncard_isLoopAt ``Submission.Graph.ncard_inc_add_ncard_isLoopAt

/-! ### The handshake lemma -/

open _root_.Graph in
/-- Counting the elements of a set cut out by a predicate, as a sum of indicators over any
`Finset` containing it. This is the bridge between `Set.ncard` and `Finset.sum` used twice in
each direction by the handshake proof. -/
private theorem ncard_setOf_eq_sum_ite {γ : Type*} (s : Finset γ) (p : γ → Prop)
    [DecidablePred p] (hsub : ∀ z, p z → z ∈ s) :
    {z | p z}.ncard = ∑ z ∈ s, if p z then 1 else 0 := by
  rw [← Finset.card_filter p s, ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨hsub z h, h⟩, fun h => h.2⟩

run_cmd do
  let target := ``Submission.Graph.ncard_setOf_eq_sum_ite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Graph.ncard_setOf_eq_sum_ite target :: scope.openDecls } }

open _root_.Graph in
/-- **The handshake lemma.** The degrees of the vertices of a finite multigraph add up to
twice the number of edges.

The proof is the double count: `G.degree x` is a sum over the edges of the number of ends
that edge has at `x`, the two sums commute, and each edge contributes exactly two
(`Graph.ncard_inc_add_ncard_isLoopAt`). Loops are allowed — that is exactly what the loop
term in `Graph.degree` buys. -/
theorem sum_degree_eq_two_mul_ncard_edgeSet (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * E(G).ncard := by
  classical
  -- `ends e x` is the number of ends of `e` at `x`.
  set ends : β → α → ℕ :=
    fun e x => (if G.Inc e x then 1 else 0) + (if G.IsLoopAt e x then 1 else 0) with hends
  -- Read the degree as a sum over the edges.
  have hdeg : ∀ x, G.degree x = ∑ e ∈ G.edgeFinset, ends e x := by
    intro x
    have h1 : (G.incidenceSet x).ncard = ∑ e ∈ G.edgeFinset, if G.Inc e x then 1 else 0 := by
      rw [incidenceSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    have h2 : (G.loopSet x).ncard = ∑ e ∈ G.edgeFinset, if G.IsLoopAt e x then 1 else 0 := by
      rw [loopSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    rw [degree_def, h1, h2, hends, ← Finset.sum_add_distrib]
  -- Each edge has exactly two ends among the vertices.
  have hedge : ∀ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x = 2 := by
    intro e he
    rw [mem_edgeFinset] at he
    have h1 : {x | G.Inc e x}.ncard = ∑ x ∈ G.vertexFinset, if G.Inc e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    have h2 : {x | G.IsLoopAt e x}.ncard
        = ∑ x ∈ G.vertexFinset, if G.IsLoopAt e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    rw [hends, Finset.sum_add_distrib, ← h1, ← h2]
    exact G.ncard_inc_add_ncard_isLoopAt he
  calc ∑ x ∈ G.vertexFinset, G.degree x
      = ∑ x ∈ G.vertexFinset, ∑ e ∈ G.edgeFinset, ends e x := by
        exact Finset.sum_congr rfl fun x _ => hdeg x
    _ = ∑ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x := Finset.sum_comm
    _ = ∑ _e ∈ G.edgeFinset, 2 := Finset.sum_congr rfl hedge
    _ = 2 * E(G).ncard := by
        rw [Finset.sum_const, card_edgeFinset, smul_eq_mul, Nat.mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.sum_degree_eq_two_mul_ncard_edgeSet then
    throwError "Refusing to shadow existing declaration Graph.sum_degree_eq_two_mul_ncard_edgeSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.sum_degree_eq_two_mul_ncard_edgeSet ``Submission.Graph.sum_degree_eq_two_mul_ncard_edgeSet

open _root_.Graph in
/-- The handshake lemma, with the edge count as a `Finset` cardinality. -/
theorem sum_degree_eq_two_mul_card_edgeFinset (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * G.edgeFinset.card := by
  rw [card_edgeFinset]
  exact G.sum_degree_eq_two_mul_ncard_edgeSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.sum_degree_eq_two_mul_card_edgeFinset then
    throwError "Refusing to shadow existing declaration Graph.sum_degree_eq_two_mul_card_edgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.sum_degree_eq_two_mul_card_edgeFinset ``Submission.Graph.sum_degree_eq_two_mul_card_edgeFinset

open _root_.Graph in
/-- The degree sum of a finite multigraph is even. -/
theorem even_sum_degree (G : Graph α β) [G.Finite] :
    Even (∑ x ∈ G.vertexFinset, G.degree x) :=
  ⟨E(G).ncard, by rw [G.sum_degree_eq_two_mul_ncard_edgeSet, two_mul]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.even_sum_degree then
    throwError "Refusing to shadow existing declaration Graph.even_sum_degree"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.even_sum_degree ``Submission.Graph.even_sum_degree

/-! ### Leaves -/

open _root_.Graph in
/-- `G.IsLeaf x` says that `x` is a vertex of `G` with exactly one edge end at it. -/
def IsLeaf (G : Graph α β) (x : α) : Prop := x ∈ V(G) ∧ G.degree x = 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf ``Submission.Graph.IsLeaf

theorem IsLeaf.mem_vertexSet (h : G.IsLeaf x) : x ∈ V(G) := h.1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Graph.IsLeaf
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.mem_vertexSet then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.mem_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.mem_vertexSet ``Submission.Graph.IsLeaf.mem_vertexSet

theorem IsLeaf.degree_eq_one (h : G.IsLeaf x) : G.degree x = 1 := h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.degree_eq_one then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.degree_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.degree_eq_one ``Submission.Graph.IsLeaf.degree_eq_one

open _root_.Graph in
theorem isLeaf_iff : G.IsLeaf x ↔ x ∈ V(G) ∧ G.degree x = 1 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.isLeaf_iff then
    throwError "Refusing to shadow existing declaration Graph.isLeaf_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.isLeaf_iff ``Submission.Graph.isLeaf_iff

/-- A leaf carries no loop: a loop would contribute two to the degree. -/
theorem IsLeaf.not_isLoopAt [G.Finite] (h : G.IsLeaf x) (e : β) : ¬ G.IsLoopAt e x := by
  intro hl
  have h2 := hl.two_le_degree
  have hd := h.2
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.not_isLoopAt then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.not_isLoopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.not_isLoopAt ``Submission.Graph.IsLeaf.not_isLoopAt

/-- The one edge end at a leaf comes from one incident edge. -/
theorem IsLeaf.ncard_incidenceSet [G.Finite] (h : G.IsLeaf x) :
    (G.incidenceSet x).ncard = 1 := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.ncard_incidenceSet then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.ncard_incidenceSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.ncard_incidenceSet ``Submission.Graph.IsLeaf.ncard_incidenceSet

theorem IsLeaf.loopSet_eq_empty [G.Finite] (h : G.IsLeaf x) : G.loopSet x = ∅ := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  have : (G.loopSet x).ncard = 0 := by omega
  exact (Set.ncard_eq_zero (finite_loopSet x)).1 this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.loopSet_eq_empty then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.loopSet_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.loopSet_eq_empty ``Submission.Graph.IsLeaf.loopSet_eq_empty

/-- A leaf is incident with exactly one edge. -/
theorem IsLeaf.existsUnique_inc [G.Finite] (h : G.IsLeaf x) : ∃! e, G.Inc e x := by
  obtain ⟨e, he⟩ := Set.ncard_eq_one.1 h.ncard_incidenceSet
  refine ⟨e, ?_, fun f hf => ?_⟩
  · have : e ∈ G.incidenceSet x := by rw [he]; rfl
    exact this
  · have : f ∈ G.incidenceSet x := hf
    rw [he] at this
    exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.existsUnique_inc then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.existsUnique_inc"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.existsUnique_inc ``Submission.Graph.IsLeaf.existsUnique_inc

/-- The unique edge at a leaf is not a loop, so it has a second, different end. -/
theorem IsLeaf.exists_isLink [G.Finite] (h : G.IsLeaf x) :
    ∃ e y, y ≠ x ∧ G.IsLink e x y := by
  obtain ⟨e, he, -⟩ := h.existsUnique_inc
  obtain ⟨y, hy⟩ := he
  refine ⟨e, y, ?_, hy⟩
  rintro rfl
  exact h.not_isLoopAt e hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.exists_isLink then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.exists_isLink"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.exists_isLink ``Submission.Graph.IsLeaf.exists_isLink

/-- Every edge at a leaf is a non-loop edge there. -/
theorem IsLeaf.isNonloopAt [G.Finite] (h : G.IsLeaf x) (he : G.Inc e x) :
    G.IsNonloopAt e x :=
  he.isLoopAt_or_isNonloopAt.resolve_left (h.not_isLoopAt e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsLeaf.isNonloopAt then
    throwError "Refusing to shadow existing declaration Graph.IsLeaf.isNonloopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsLeaf.isNonloopAt ``Submission.Graph.IsLeaf.isNonloopAt

open _root_.Graph in
/-- The converse of the two lemmas above: a vertex of `G` whose only incident edge is `e`,
and for which `e` is not a loop, is a leaf. -/
theorem isLeaf_of_isNonloopAt (hx : x ∈ V(G))
    (h : ∀ f, G.Inc f x ↔ f = e) (hne : G.IsNonloopAt e x) : G.IsLeaf x := by
  refine ⟨hx, ?_⟩
  have h1 : G.incidenceSet x = {e} := by
    ext f
    simpa using h f
  have h2 : G.loopSet x = ∅ := by
    ext f
    simp only [_root_.Graph.mem_loopSet, Set.mem_empty_iff_false, iff_false]
    intro hf
    exact hne.not_isLoopAt x (((h f).1 hf.inc) ▸ hf)
  rw [degree_def, h1, h2]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.isLeaf_of_isNonloopAt then
    throwError "Refusing to shadow existing declaration Graph.isLeaf_of_isNonloopAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.isLeaf_of_isNonloopAt ``Submission.Graph.isLeaf_of_isNonloopAt

end Graph
