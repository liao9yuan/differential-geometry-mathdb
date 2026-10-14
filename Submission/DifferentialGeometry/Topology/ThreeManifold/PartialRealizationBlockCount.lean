import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationStepAssembly
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

def blockEdgeFinset (S : Finset G.Edge) (v : G.Vertex) : Finset G.Edge := by
  classical
  exact S.filter fun e => G.source e ∈ G.vertexBlock S v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset

theorem mem_blockEdgeFinset (S : Finset G.Edge) (v : G.Vertex) (e : G.Edge) :
    e ∈ G.blockEdgeFinset S v ↔ e ∈ S ∧ G.source e ∈ G.vertexBlock S v := by
  classical
  simp only [blockEdgeFinset, Finset.mem_filter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockEdgeFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockEdgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockEdgeFinset ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockEdgeFinset

theorem vertexBlock_eq_of_reachable (S : Finset G.Edge) {v v' : G.Vertex}
    (h : (G.processedGraph S).Reachable v v') : G.vertexBlock S v = G.vertexBlock S v' := by
  classical
  ext w
  rw [mem_vertexBlock G S v w, mem_vertexBlock G S v' w]
  exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_of_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_of_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_of_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_of_reachable

theorem blockEdgeFinset_eq_of_reachable (S : Finset G.Edge) {v v' : G.Vertex}
    (h : (G.processedGraph S).Reachable v v') :
    G.blockEdgeFinset S v = G.blockEdgeFinset S v' := by
  classical
  simp only [blockEdgeFinset, vertexBlock_eq_of_reachable G S h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_eq_of_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_eq_of_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_eq_of_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_eq_of_reachable

theorem blockEdgeFinset_empty (v : G.Vertex) : G.blockEdgeFinset ∅ v = ∅ := by
  classical
  ext e
  rw [mem_blockEdgeFinset]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_empty

theorem blockEdgeFinset_insert_of_reachable_of_mem (S : Finset G.Edge) (e : G.Edge)
    (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : (G.processedGraph S).Reachable v (G.source e)) :
    G.blockEdgeFinset (_root_.Insert.insert e S) v = _root_.Insert.insert e (G.blockEdgeFinset S v) := by
  classical
  have hv' : G.source e ∈ G.vertexBlock S v :=
    (mem_vertexBlock G S v (G.source e)).mpr hv
  ext f
  rw [mem_blockEdgeFinset, Finset.mem_insert, Finset.mem_insert,
    vertexBlock_insert_of_reachable G S e h v, mem_blockEdgeFinset]
  constructor
  · rintro ⟨hf, hfs⟩
    rcases hf with hfe | hf
    · exact Or.inl hfe
    · exact Or.inr ⟨hf, hfs⟩
  · rintro (rfl | ⟨hf, hfs⟩)
    · exact ⟨Or.inl rfl, hv'⟩
    · exact ⟨Or.inr hf, hfs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_mem ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_mem

theorem blockEdgeFinset_insert_of_reachable_of_not_mem (S : Finset G.Edge) (e : G.Edge)
    (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : ¬ (G.processedGraph S).Reachable v (G.source e)) :
    G.blockEdgeFinset (_root_.Insert.insert e S) v = G.blockEdgeFinset S v := by
  classical
  have hvs : G.source e ∉ G.vertexBlock S v :=
    fun hmem => hv ((mem_vertexBlock G S v (G.source e)).mp hmem)
  ext f
  rw [mem_blockEdgeFinset, mem_blockEdgeFinset,
    vertexBlock_insert_of_reachable G S e h v]
  constructor
  · rintro ⟨hf, hfs⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact absurd hfs hvs
    · exact ⟨hf, hfs⟩
  · rintro ⟨hf, hfs⟩
    exact ⟨Finset.mem_insert_of_mem hf, hfs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_not_mem ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_reachable_of_not_mem

theorem vertexBlock_insert_eq_of_not_reachable (S : Finset G.Edge) (e : G.Edge) (v : G.Vertex)
    (hvs : ¬ (G.processedGraph S).Reachable v (G.source e))
    (hvt : ¬ (G.processedGraph S).Reachable v (G.target e)) :
    G.vertexBlock (_root_.Insert.insert e S) v = G.vertexBlock S v := by
  classical
  ext w
  rw [mem_vertexBlock G (_root_.Insert.insert e S) v w, mem_vertexBlock G S v w,
    G.processedGraph_reachable_insert S e v w]
  constructor
  · rintro (h | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact h
    · exact absurd h1 hvs
    · exact absurd h1 hvt
  · exact Or.inl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_eq_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_eq_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_eq_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_eq_of_not_reachable

theorem blockEdgeFinset_insert_eq_of_not_reachable (S : Finset G.Edge) (e : G.Edge) (v : G.Vertex)
    (hvs : ¬ (G.processedGraph S).Reachable v (G.source e))
    (hvt : ¬ (G.processedGraph S).Reachable v (G.target e)) :
    G.blockEdgeFinset (_root_.Insert.insert e S) v = G.blockEdgeFinset S v := by
  classical
  have hvb := vertexBlock_insert_eq_of_not_reachable G S e v hvs hvt
  have hvs' : G.source e ∉ G.vertexBlock S v :=
    fun hmem => hvs ((mem_vertexBlock G S v (G.source e)).mp hmem)
  ext f
  rw [mem_blockEdgeFinset, mem_blockEdgeFinset, hvb]
  constructor
  · rintro ⟨hf, hfs⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact absurd hfs hvs'
    · exact ⟨hf, hfs⟩
  · rintro ⟨hf, hfs⟩
    exact ⟨Finset.mem_insert_of_mem hf, hfs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_eq_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_eq_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_eq_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_eq_of_not_reachable

theorem vertexBlock_insert_of_not_reachable_of_reachable_ends [DecidableEq G.Vertex]
    (S : Finset G.Edge) (e : G.Edge)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : (G.processedGraph S).Reachable v (G.source e) ∨
      (G.processedGraph S).Reachable v (G.target e)) :
    G.vertexBlock (_root_.Insert.insert e S) v =
      G.vertexBlock S (G.source e) ∪ G.vertexBlock S (G.target e) := by
  classical
  have hle : G.processedGraph S ≤ G.processedGraph (_root_.Insert.insert e S) :=
    processedGraph_mono G fun f hf => Finset.mem_insert_of_mem hf
  rcases hv with hv | hv
  · rw [vertexBlock_eq_of_reachable G (_root_.Insert.insert e S) (SimpleGraph.Reachable.mono hle hv),
      vertexBlock_insert_of_not_reachable G S e h]
  · rw [vertexBlock_eq_of_reachable G (_root_.Insert.insert e S) (SimpleGraph.Reachable.mono hle hv),
      vertexBlock_eq_of_reachable G (_root_.Insert.insert e S)
        (reachable_source_target_insert G S e).symm,
      vertexBlock_insert_of_not_reachable G S e h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable_of_reachable_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable_of_reachable_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable_of_reachable_ends ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable_of_reachable_ends

theorem blockEdgeFinset_insert_of_not_reachable_of_reachable_ends
    (S : Finset G.Edge) (e : G.Edge)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : (G.processedGraph S).Reachable v (G.source e) ∨
      (G.processedGraph S).Reachable v (G.target e)) :
    G.blockEdgeFinset (_root_.Insert.insert e S) v =
      insert e (G.blockEdgeFinset S (G.source e) ∪ G.blockEdgeFinset S (G.target e)) := by
  classical
  have hle : G.processedGraph S ≤ G.processedGraph (_root_.Insert.insert e S) :=
    processedGraph_mono G fun f hf => Finset.mem_insert_of_mem hf
  have hreach : (G.processedGraph (_root_.Insert.insert e S)).Reachable v (G.source e) :=
    Or.elim hv (fun h1 => SimpleGraph.Reachable.mono hle h1)
      fun h1 => (SimpleGraph.Reachable.mono hle h1).trans
        (reachable_source_target_insert G S e).symm
  rw [blockEdgeFinset_eq_of_reachable G (_root_.Insert.insert e S) hreach, blockEdgeFinset, blockEdgeFinset,
    blockEdgeFinset, vertexBlock_insert_of_not_reachable G S e h]
  ext f
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_insert, Finset.mem_union,
    Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    rcases hfirst with hfe | hfS
    · exact Or.inl hfe
    · rcases hsecond with h1 | h1
      · exact Or.inr (Or.inl ⟨hfS, h1⟩)
      · exact Or.inr (Or.inr ⟨hfS, h1⟩)
  · rintro (hfe | ⟨hfS, h1⟩ | ⟨hfS, h1⟩)
    · rw [hfe]
      exact ⟨Or.inl rfl,
        Or.inl ((mem_vertexBlock G S (G.source e) (G.source e)).mpr
          (SimpleGraph.Reachable.refl _))⟩
    · exact ⟨Or.inr hfS, Or.inl h1⟩
    · exact ⟨Or.inr hfS, Or.inr h1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_not_reachable_of_reachable_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_not_reachable_of_reachable_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_not_reachable_of_reachable_ends ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_insert_of_not_reachable_of_reachable_ends

theorem disjoint_blockEdgeFinset_of_not_reachable (S : Finset G.Edge) (e : G.Edge)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) :
    Disjoint (G.blockEdgeFinset S (G.source e)) (G.blockEdgeFinset S (G.target e)) := by
  classical
  rw [Finset.disjoint_left]
  intro f hf hf'
  rw [mem_blockEdgeFinset] at hf hf'
  exact h (((mem_vertexBlock G S (G.source e) (G.source f)).mp hf.2).trans
    (((mem_vertexBlock G S (G.target e) (G.source f)).mp hf'.2).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_blockEdgeFinset_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_blockEdgeFinset_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_blockEdgeFinset_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_blockEdgeFinset_of_not_reachable

theorem card_vertexBlock_le_card_blockEdgeFinset_add_one (S : Finset G.Edge) (v : G.Vertex) :
    (G.vertexBlock S v).card ≤ (G.blockEdgeFinset S v).card + 1 := by
  classical
  revert v
  refine Finset.induction_on S (motive := fun S => ∀ v : G.Vertex,
    (G.vertexBlock S v).card ≤ (G.blockEdgeFinset S v).card + 1) ?_ ?_
  · intro v
    rw [vertexBlock_empty, blockEdgeFinset_empty]
    simp
  · intro e S he ih v
    by_cases h : (G.processedGraph S).Reachable (G.source e) (G.target e)
    · by_cases hv : (G.processedGraph S).Reachable v (G.source e)
      · have hvb := vertexBlock_insert_of_reachable G S e h v
        have heq := blockEdgeFinset_insert_of_reachable_of_mem G S e h v hv
        have hmem : e ∉ G.blockEdgeFinset S v :=
          fun hmem => he ((mem_blockEdgeFinset G S v e).mp hmem).1
        rw [hvb, heq, Finset.card_insert_of_notMem hmem]
        have := ih v
        omega
      · have hvb := vertexBlock_insert_of_reachable G S e h v
        have heq := blockEdgeFinset_insert_of_reachable_of_not_mem G S e h v hv
        rw [hvb, heq]
        exact ih v
    · by_cases hv : (G.processedGraph S).Reachable v (G.source e) ∨
          (G.processedGraph S).Reachable v (G.target e)
      · have hvb := vertexBlock_insert_of_not_reachable_of_reachable_ends G S e h v hv
        have heq := blockEdgeFinset_insert_of_not_reachable_of_reachable_ends G S e h v hv
        have hmem : e ∉ G.blockEdgeFinset S (G.source e) ∪
            G.blockEdgeFinset S (G.target e) := by
          intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h1
          · exact he ((mem_blockEdgeFinset G S (G.source e) e).mp h1).1
          · exact he ((mem_blockEdgeFinset G S (G.target e) e).mp h1).1
        rw [hvb, heq, Finset.card_insert_of_notMem hmem,
          Finset.card_union_of_disjoint
            (disjoint_vertexBlock_of_not_reachable G S e h),
          Finset.card_union_of_disjoint (disjoint_blockEdgeFinset_of_not_reachable G S e h)]
        have h1 := ih (G.source e)
        have h2 := ih (G.target e)
        omega
      · have hvs : ¬ (G.processedGraph S).Reachable v (G.source e) := fun h1 => hv (Or.inl h1)
        have hvt : ¬ (G.processedGraph S).Reachable v (G.target e) := fun h1 => hv (Or.inr h1)
        have hvb := vertexBlock_insert_eq_of_not_reachable G S e v hvs hvt
        have heq := blockEdgeFinset_insert_eq_of_not_reachable G S e v hvs hvt
        rw [hvb, heq]
        exact ih v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.card_vertexBlock_le_card_blockEdgeFinset_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.card_vertexBlock_le_card_blockEdgeFinset_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.card_vertexBlock_le_card_blockEdgeFinset_add_one ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.card_vertexBlock_le_card_blockEdgeFinset_add_one

def blockExponent (S : Finset G.Edge) (v : G.Vertex) : ℕ :=
  (G.blockEdgeFinset S v).card + 1 - (G.vertexBlock S v).card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent

theorem blockExponent_add_card_vertexBlock (S : Finset G.Edge) (v : G.Vertex) :
    G.blockExponent S v + (G.vertexBlock S v).card = (G.blockEdgeFinset S v).card + 1 := by
  have h := card_vertexBlock_le_card_blockEdgeFinset_add_one G S v
  simp only [blockExponent]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_vertexBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_vertexBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_vertexBlock ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_vertexBlock

theorem blockExponent_empty (v : G.Vertex) : G.blockExponent ∅ v = 0 := by
  classical
  rw [blockExponent, blockEdgeFinset_empty, vertexBlock_empty]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_empty

theorem blockExponent_insert_of_reachable_of_mem (S : Finset G.Edge) (e : G.Edge)
    (he : e ∉ S) (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : (G.processedGraph S).Reachable v (G.source e)) :
    G.blockExponent (_root_.Insert.insert e S) v = G.blockExponent S v + 1 := by
  have hvb := vertexBlock_insert_of_reachable G S e h v
  have heq := blockEdgeFinset_insert_of_reachable_of_mem G S e h v hv
  have hmem : e ∉ G.blockEdgeFinset S v :=
    fun hmem => he ((mem_blockEdgeFinset G S v e).mp hmem).1
  have hle := card_vertexBlock_le_card_blockEdgeFinset_add_one G S v
  simp only [blockExponent, hvb, heq, Finset.card_insert_of_notMem hmem]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_mem ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_mem

theorem blockExponent_insert_of_reachable_of_not_mem (S : Finset G.Edge) (e : G.Edge)
    (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : ¬ (G.processedGraph S).Reachable v (G.source e)) :
    G.blockExponent (_root_.Insert.insert e S) v = G.blockExponent S v := by
  rw [blockExponent, blockExponent, vertexBlock_insert_of_reachable G S e h v,
    blockEdgeFinset_insert_of_reachable_of_not_mem G S e h v hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_not_mem ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_reachable_of_not_mem

theorem blockExponent_insert_of_not_reachable_of_reachable_ends
    (S : Finset G.Edge) (e : G.Edge) (he : e ∉ S)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex)
    (hv : (G.processedGraph S).Reachable v (G.source e) ∨
      (G.processedGraph S).Reachable v (G.target e)) :
    G.blockExponent (_root_.Insert.insert e S) v =
      G.blockExponent S (G.source e) + G.blockExponent S (G.target e) := by
  classical
  have hvb := vertexBlock_insert_of_not_reachable_of_reachable_ends G S e h v hv
  have heq := blockEdgeFinset_insert_of_not_reachable_of_reachable_ends G S e h v hv
  have hmem : e ∉ G.blockEdgeFinset S (G.source e) ∪ G.blockEdgeFinset S (G.target e) := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h1
    · exact he ((mem_blockEdgeFinset G S (G.source e) e).mp h1).1
    · exact he ((mem_blockEdgeFinset G S (G.target e) e).mp h1).1
  have h1 := card_vertexBlock_le_card_blockEdgeFinset_add_one G S (G.source e)
  have h2 := card_vertexBlock_le_card_blockEdgeFinset_add_one G S (G.target e)
  simp only [blockExponent, hvb, heq, Finset.card_insert_of_notMem hmem,
    Finset.card_union_of_disjoint (disjoint_vertexBlock_of_not_reachable G S e h),
    Finset.card_union_of_disjoint (disjoint_blockEdgeFinset_of_not_reachable G S e h)]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_reachable_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_reachable_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_reachable_ends ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_reachable_ends

theorem blockExponent_insert_of_not_reachable_of_not_reachable (S : Finset G.Edge) (e : G.Edge)
    (v : G.Vertex)
    (hvs : ¬ (G.processedGraph S).Reachable v (G.source e))
    (hvt : ¬ (G.processedGraph S).Reachable v (G.target e)) :
    G.blockExponent (_root_.Insert.insert e S) v = G.blockExponent S v := by
  rw [blockExponent, blockExponent, vertexBlock_insert_eq_of_not_reachable G S e v hvs hvt,
    blockEdgeFinset_insert_eq_of_not_reachable G S e v hvs hvt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_insert_of_not_reachable_of_not_reachable

theorem blockEdgeFinset_univ_of_preconnected (v : G.Vertex)
    (h : (G.processedGraph Finset.univ).Preconnected) :
    G.blockEdgeFinset Finset.univ v = Finset.univ := by
  classical
  rw [blockEdgeFinset, vertexBlock_eq_univ_of_preconnected G Finset.univ v h]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_univ_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_univ_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_univ_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdgeFinset_univ_of_preconnected

theorem blockExponent_add_card_eq_card_edge_add_one (v : G.Vertex)
    (h : (G.processedGraph Finset.univ).Preconnected) :
    G.blockExponent Finset.univ v + Fintype.card G.Vertex = Fintype.card G.Edge + 1 := by
  classical
  have h1 := blockExponent_add_card_vertexBlock G Finset.univ v
  rw [vertexBlock_eq_univ_of_preconnected G Finset.univ v h,
    blockEdgeFinset_univ_of_preconnected G v h] at h1
  simpa using h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_eq_card_edge_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_eq_card_edge_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_eq_card_edge_add_one ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_add_card_eq_card_edge_add_one

theorem blockExponent_univ_eq_card_edge_sub_add_one (v : G.Vertex)
    (h : (G.processedGraph Finset.univ).Preconnected) :
    G.blockExponent Finset.univ v = Fintype.card G.Edge + 1 - Fintype.card G.Vertex := by
  have h1 := blockExponent_add_card_eq_card_edge_add_one G v h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_univ_eq_card_edge_sub_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_univ_eq_card_edge_sub_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_univ_eq_card_edge_sub_add_one ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_univ_eq_card_edge_sub_add_one

def blockSet (S : Finset G.Edge) : Finset (Finset G.Vertex) := by
  classical
  exact Finset.univ.image fun v => G.vertexBlock S v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet

def blockCount (S : Finset G.Edge) : ℕ := (G.blockSet S).card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount

def blockExponentOfBlock [DecidableEq G.Vertex] (S : Finset G.Edge) (B : Finset G.Vertex) : ℕ :=
  (S.filter fun e => G.source e ∈ B).card + 1 - B.card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock

theorem mem_blockSet (S : Finset G.Edge) (B : Finset G.Vertex) :
    B ∈ G.blockSet S ↔ ∃ v : G.Vertex, G.vertexBlock S v = B := by
  classical
  simp only [blockSet, Finset.mem_image, Finset.mem_univ, true_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_blockSet

theorem vertexBlock_filter_eq_of_mem_blockSet [DecidableEq G.Vertex] (S : Finset G.Edge)
    {B : Finset G.Vertex}
    (hB : B ∈ G.blockSet S) :
    (Finset.univ.filter fun v : G.Vertex => G.vertexBlock S v = B) = B := by
  classical
  obtain ⟨w, rfl⟩ := (mem_blockSet G S B).mp hB
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    exact hv ▸ ((mem_vertexBlock G S v v).mpr (SimpleGraph.Reachable.refl v))
  · intro hv
    exact (vertexBlock_eq_of_reachable G S ((mem_vertexBlock G S w v).mp hv)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_filter_eq_of_mem_blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_filter_eq_of_mem_blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_filter_eq_of_mem_blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_filter_eq_of_mem_blockSet

theorem sum_card_blockSet (S : Finset G.Edge) :
    (G.blockSet S).sum (fun B => B.card) = Fintype.card G.Vertex := by
  classical
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : G.Vertex => G.vertexBlock S v)
    (t := G.blockSet S) fun v _ => (mem_blockSet G S _).mpr ⟨v, rfl⟩]
  exact Finset.sum_congr rfl fun B hB => by
    rw [vertexBlock_filter_eq_of_mem_blockSet G S hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockSet

theorem blockEdge_filter_eq_of_mem_blockSet [DecidableEq G.Vertex] (S : Finset G.Edge)
    {B : Finset G.Vertex}
    (hB : B ∈ G.blockSet S) :
    (S.filter fun e : G.Edge => G.vertexBlock S (G.source e) = B) =
      S.filter fun e : G.Edge => G.source e ∈ B := by
  classical
  obtain ⟨w, rfl⟩ := (mem_blockSet G S B).mp hB
  refine Finset.filter_congr fun e _ => ?_
  constructor
  · intro h
    exact h ▸
      ((mem_vertexBlock G S (G.source e) (G.source e)).mpr (SimpleGraph.Reachable.refl _))
  · intro h
    exact (vertexBlock_eq_of_reachable G S ((mem_vertexBlock G S w (G.source e)).mp h)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdge_filter_eq_of_mem_blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdge_filter_eq_of_mem_blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdge_filter_eq_of_mem_blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockEdge_filter_eq_of_mem_blockSet

theorem sum_card_blockEdgeFinset [DecidableEq G.Vertex] (S : Finset G.Edge) :
    (G.blockSet S).sum (fun B => (S.filter fun e : G.Edge => G.source e ∈ B).card) = S.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e : G.Edge => G.vertexBlock S (G.source e))
    (t := G.blockSet S)
    fun e _ => (mem_blockSet G S _).mpr ⟨G.source e, rfl⟩]
  exact Finset.sum_congr rfl fun B hB => by
    rw [blockEdge_filter_eq_of_mem_blockSet G S hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockEdgeFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockEdgeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockEdgeFinset ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.sum_card_blockEdgeFinset

theorem card_le_card_blockEdge_of_mem_blockSet [DecidableEq G.Vertex] (S : Finset G.Edge)
    {B : Finset G.Vertex}
    (hB : B ∈ G.blockSet S) :
    B.card ≤ (S.filter fun e : G.Edge => G.source e ∈ B).card + 1 := by
  classical
  obtain ⟨w, rfl⟩ := (mem_blockSet G S B).mp hB
  have hbridge : (S.filter fun e : G.Edge => G.source e ∈ G.vertexBlock S w) =
      G.blockEdgeFinset S w := by
    rw [blockEdgeFinset]
    exact (Finset.filter_congr_decidable S _ _).symm
  rw [hbridge]
  exact card_vertexBlock_le_card_blockEdgeFinset_add_one G S w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.card_le_card_blockEdge_of_mem_blockSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.card_le_card_blockEdge_of_mem_blockSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.card_le_card_blockEdge_of_mem_blockSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.card_le_card_blockEdge_of_mem_blockSet

theorem blockExponentOfBlock_add_card [DecidableEq G.Vertex] (S : Finset G.Edge)
    {B : Finset G.Vertex}
    (hB : B ∈ G.blockSet S) :
    G.blockExponentOfBlock S B + B.card =
      (S.filter fun e : G.Edge => G.source e ∈ B).card + 1 := by
  have h := card_le_card_blockEdge_of_mem_blockSet G S hB
  rw [blockExponentOfBlock]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock_add_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock_add_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock_add_card ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponentOfBlock_add_card

theorem sum_blockExponentOfBlock_add_card_vertex_eq_card_add_blockCount [DecidableEq G.Vertex]
    (S : Finset G.Edge) :
    (G.blockSet S).sum (fun B => G.blockExponentOfBlock S B) + Fintype.card G.Vertex =
      S.card + G.blockCount S := by
  classical
  calc (G.blockSet S).sum (fun B => G.blockExponentOfBlock S B) + Fintype.card G.Vertex
      = (G.blockSet S).sum (fun B => G.blockExponentOfBlock S B) +
          (G.blockSet S).sum (fun B => B.card) := by rw [sum_card_blockSet]
    _ = (G.blockSet S).sum (fun B => G.blockExponentOfBlock S B + B.card) := by
          rw [Finset.sum_add_distrib]
    _ = (G.blockSet S).sum
          (fun B => (S.filter fun e : G.Edge => G.source e ∈ B).card + 1) :=
          Finset.sum_congr rfl fun B hB => blockExponentOfBlock_add_card G S hB
    _ = (G.blockSet S).sum (fun B => (S.filter fun e : G.Edge => G.source e ∈ B).card) +
          (G.blockSet S).sum (fun _ => 1) := by rw [Finset.sum_add_distrib]
    _ = S.card + G.blockCount S := by
          rw [sum_card_blockEdgeFinset, blockCount]
          congr 1
          exact (Finset.card_eq_sum_ones (G.blockSet S)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_blockExponentOfBlock_add_card_vertex_eq_card_add_blockCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.sum_blockExponentOfBlock_add_card_vertex_eq_card_add_blockCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.sum_blockExponentOfBlock_add_card_vertex_eq_card_add_blockCount ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.sum_blockExponentOfBlock_add_card_vertex_eq_card_add_blockCount

theorem blockSet_eq_singleton_univ_of_preconnected (S : Finset G.Edge) (v : G.Vertex)
    (h : (G.processedGraph S).Preconnected) : G.blockSet S = {Finset.univ} := by
  classical
  ext B
  rw [mem_blockSet, Finset.mem_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    exact vertexBlock_eq_univ_of_preconnected G S w h
  · intro hB
    exact ⟨v, by rw [hB]; exact vertexBlock_eq_univ_of_preconnected G S v h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet_eq_singleton_univ_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet_eq_singleton_univ_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet_eq_singleton_univ_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockSet_eq_singleton_univ_of_preconnected

theorem blockCount_eq_one_of_preconnected (S : Finset G.Edge) (v : G.Vertex)
    (h : (G.processedGraph S).Preconnected) : G.blockCount S = 1 := by
  rw [blockCount, blockSet_eq_singleton_univ_of_preconnected G S v h]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount_eq_one_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount_eq_one_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount_eq_one_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCount_eq_one_of_preconnected

def BlockCountBalance (G : MarkedManifoldGraph.{u}) : Prop :=
  ∀ v : G.Vertex, G.blockExponent Finset.univ v + Fintype.card G.Vertex =
    Fintype.card G.Edge + 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.BlockCountBalance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.BlockCountBalance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.BlockCountBalance ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.BlockCountBalance

theorem blockCountBalance_of_preconnected (h : (G.processedGraph Finset.univ).Preconnected) :
    G.BlockCountBalance := fun v => blockExponent_add_card_eq_card_edge_add_one G v h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_of_preconnected

theorem blockCountBalance_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3) :
    (oneVertex N).BlockCountBalance :=
  blockCountBalance_of_preconnected (oneVertex N) fun _ _ => SimpleGraph.Reachable.of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertex

theorem blockCountBalance_twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    (twoVertex N B B').BlockCountBalance := by
  refine blockCountBalance_of_preconnected (twoVertex N B B') ?_
  intro a b
  have hle : (twoVertex N B B').processedGraph (_root_.Insert.insert PUnit.unit ∅) ≤
      (twoVertex N B B').processedGraph Finset.univ :=
    processedGraph_mono (twoVertex N B B')
      fun f _ => Finset.mem_univ f
  have hreach := reachable_twoVertex_insert N B B'
  cases a <;> cases b
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.mono hle hreach
  · exact (SimpleGraph.Reachable.mono hle hreach).symm
  · exact SimpleGraph.Reachable.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_twoVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_twoVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_twoVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_twoVertex

theorem not_blockCountBalance_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    ¬ (twoVertexEmpty N N').BlockCountBalance := by
  classical
  intro h
  have h' := h _root_.Bool.false
  have huniv : (Finset.univ : Finset (twoVertexEmpty N N').Edge) = ∅ := Finset.univ_eq_empty
  rw [huniv, blockExponent, blockEdgeFinset_empty, vertexBlock_empty] at h'
  simp at h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_blockCountBalance_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_blockCountBalance_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_blockCountBalance_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_blockCountBalance_twoVertexEmpty

theorem blockExponent_oneVertexLoop (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (h : Disjoint B.collar B'.collar) :
    (oneVertexLoop N B B' h).blockExponent Finset.univ PUnit.unit = 1 := by
  rw [blockExponent_univ_eq_card_edge_sub_add_one (oneVertexLoop N B B' h) PUnit.unit
    fun _ _ => SimpleGraph.Reachable.of_subsingleton]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_oneVertexLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_oneVertexLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_oneVertexLoop ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockExponent_oneVertexLoop

theorem blockCountBalance_oneVertexLoop (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (h : Disjoint B.collar B'.collar) :
    (oneVertexLoop N B B' h).BlockCountBalance :=
  blockCountBalance_of_preconnected (oneVertexLoop N B B' h)
    fun _ _ => SimpleGraph.Reachable.of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertexLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertexLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertexLoop ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockCountBalance_oneVertexLoop

end MarkedManifoldGraph

namespace PartialRealization

private theorem connectedComponents_mk_sum_inl_ne_sum_inr {X Y : ClosedOrientedManifold.{u} 3}
    (x : X.Carrier) (y : Y.Carrier) :
    ConnectedComponents.mk (Sum.inl x : X.Carrier ⊕ Y.Carrier) ≠
      ConnectedComponents.mk (Sum.inr y : X.Carrier ⊕ Y.Carrier) := by
  intro h
  have hmem : (Sum.inl x : X.Carrier ⊕ Y.Carrier) ∈ connectedComponent (Sum.inr y) :=
    ConnectedComponents.coe_eq_coe'.mp h
  have hsub : (Sum.inl x : X.Carrier ⊕ Y.Carrier) ∈ Set.range (@Sum.inr X.Carrier Y.Carrier) :=
    isPreconnected_connectedComponent.subset_isClopen
      (isClopen_range_inr (X := X.Carrier) (Y := Y.Carrier))
      ⟨Sum.inr y, mem_connectedComponent, ⟨y, rfl⟩⟩ hmem
  obtain ⟨w, hw⟩ := hsub
  exact Sum.inr_ne_inl hw

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inl_ne_sum_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inl_ne_sum_inr target :: scope.openDecls } }

private theorem connectedComponents_mk_sum_inl_eq {X Y : ClosedOrientedManifold.{u} 3}
    [PreconnectedSpace X.Carrier] (x x' : X.Carrier) :
    ConnectedComponents.mk (Sum.inl x : X.Carrier ⊕ Y.Carrier) =
      ConnectedComponents.mk (Sum.inl x') := by
  rw [← (continuous_inl (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap_mk,
    ← (continuous_inl (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap_mk]
  exact congrArg _ (Subsingleton.elim _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inl_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inl_eq target :: scope.openDecls } }

private theorem connectedComponents_mk_sum_inr_eq {X Y : ClosedOrientedManifold.{u} 3}
    [PreconnectedSpace Y.Carrier] (y y' : Y.Carrier) :
    ConnectedComponents.mk (Sum.inr y : X.Carrier ⊕ Y.Carrier) =
      ConnectedComponents.mk (Sum.inr y') := by
  rw [← (continuous_inr (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap_mk,
    ← (continuous_inr (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap_mk]
  exact congrArg _ (Subsingleton.elim _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inr_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_sum_inr_eq target :: scope.openDecls } }

def twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    PartialRealization (MarkedManifoldGraph.twoVertexEmpty N N') ∅ where
  realization :=
    ClosedOrientedManifold.sum N.toClosedOrientedManifold N'.toClosedOrientedManifold
  vertexPiece := fun v =>
    match v with
    | false => ⟨fun y => Sum.inl y.1, continuous_inl.comp continuous_subtype_val⟩
    | true => ⟨fun y => Sum.inr y.1, continuous_inr.comp continuous_subtype_val⟩
  cylinderPiece := fun e => PEmpty.elim e
  survivingFlag := fun e => PEmpty.elim e
  covers := fun x =>
    Or.inl (by
      rcases x with x | x
      · exact ⟨false, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩
      · exact ⟨true, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩)
  survivingFlag_collar_disjoint := fun e => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.twoVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.twoVertexEmpty

theorem componentCorrespondence_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    (twoVertexEmpty N N').componentCorrespondence := by
  intro v v' y y'
  constructor
  · intro h
    cases v <;> cases v'
    · exact SimpleGraph.Reachable.refl _root_.Bool.false
    · exact absurd h (connectedComponents_mk_sum_inl_ne_sum_inr y.1 y'.1)
    · exact absurd h.symm (connectedComponents_mk_sum_inl_ne_sum_inr y'.1 y.1)
    · exact SimpleGraph.Reachable.refl _root_.Bool.true
  · intro h
    cases v <;> cases v'
    · exact connectedComponents_mk_sum_inl_eq (Y := N'.toClosedOrientedManifold) y.1 y'.1
    · exact absurd h (MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty N N')
    · exact absurd h.symm (MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty N N')
    · exact connectedComponents_mk_sum_inr_eq (X := N.toClosedOrientedManifold) y.1 y'.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_twoVertexEmpty

theorem hasBlockPresentation_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3)
    (Z : ConnectedClosedOrientedManifold.{0} 3) :
    (twoVertexEmpty N N').HasBlockPresentation Z := by
  refine ⟨fun _ => 0, fun _ _ _ => rfl, fun v y => ?_⟩
  cases v
  · have hb : (finiteConnectedSum
        ((MarkedManifoldGraph.twoVertexEmpty N N').vertexBlockList ∅ _root_.Bool.false ++
          List.replicate 0 Z)).toClosedOrientedManifold = N.toClosedOrientedManifold := by
      rw [MarkedManifoldGraph.vertexBlockList_empty, List.replicate_zero, List.append_nil,
        finiteConnectedSum_singleton]
      rfl
    rw [hb]
    exact ⟨(ClosedOrientedManifold.sumComponentInl_orientedDiffeomorph
        (Y := N'.toClosedOrientedManifold) y.1).trans
      (ClosedOrientedManifold.componentOrientedDiffeomorph N.toClosedOrientedManifold
        (ConnectedComponents.mk y.1))⟩
  · have hb : (finiteConnectedSum
        ((MarkedManifoldGraph.twoVertexEmpty N N').vertexBlockList ∅ _root_.Bool.true ++
          List.replicate 0 Z)).toClosedOrientedManifold = N'.toClosedOrientedManifold := by
      rw [MarkedManifoldGraph.vertexBlockList_empty, List.replicate_zero, List.append_nil,
        finiteConnectedSum_singleton]
      rfl
    rw [hb]
    exact ⟨(ClosedOrientedManifold.sumComponentInr_orientedDiffeomorph
        (X := N.toClosedOrientedManifold) y.1).trans
      (ClosedOrientedManifold.componentOrientedDiffeomorph N'.toClosedOrientedManifold
        (ConnectedComponents.mk y.1))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.hasBlockPresentation_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.hasBlockPresentation_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.hasBlockPresentation_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.hasBlockPresentation_twoVertexEmpty

theorem cylinderComponentCovering_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    (twoVertexEmpty N N').CylinderComponentCovering := by
  intro x
  rcases x with x | x
  · exact ⟨false, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩
  · exact ⟨true, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_twoVertexEmpty

theorem isBlockInvariant_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3)
    (Z : ConnectedClosedOrientedManifold.{0} 3) :
    (twoVertexEmpty N N').IsBlockInvariant Z :=
  ⟨componentCorrespondence_twoVertexEmpty N N',
    hasBlockPresentation_twoVertexEmpty N N' Z,
    cylinderComponentCovering_twoVertexEmpty N N'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_twoVertexEmpty

end PartialRealization

theorem twoVertexEmptyBlockStepLaw (N N' : ConnectedClosedOrientedManifold.{0} 3)
    (Z : ConnectedClosedOrientedManifold.{0} 3) :
    BlockStepLaw (MarkedManifoldGraph.twoVertexEmpty N N') Z where
  initial := ⟨PartialRealization.twoVertexEmpty N N',
    PartialRealization.isBlockInvariant_twoVertexEmpty N N' Z⟩
  step := fun _ _ e _ _ => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.twoVertexEmptyBlockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.twoVertexEmptyBlockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.twoVertexEmptyBlockStepLaw ``Submission.DifferentialGeometry.Topology.twoVertexEmptyBlockStepLaw

theorem nonempty_orientedDiffeomorph_connectedSum_right
    {X Y Y' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y.toClosedOrientedManifold
      Y'.toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X Y').toClosedOrientedManifold) := by
  obtain ⟨e⟩ := h
  have hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        N.toClosedOrientedManifold)) [X, Y] [X, Y'] :=
    List.Forall₂.cons
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl X.toClosedOrientedManifold⟩
      (List.Forall₂.cons ⟨e⟩ List.Forall₂.nil)
  simpa using finiteConnectedSum_congr hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_right ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_right

theorem orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate (b b' : ℕ)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (finiteConnectedSum (List.replicate b Z))
        (finiteConnectedSum (List.replicate b' Z))).toClosedOrientedManifold
      (finiteConnectedSum (List.replicate (b + b') Z)).toClosedOrientedManifold) := by
  simpa using orientedDiffeomorph_connectedSum_finiteConnectedSum_merge
    ([] : List (ConnectedClosedOrientedManifold.{u} 3)) [] Z b b'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate

theorem orientedDiffeomorph_connectedSum_finiteConnectedSum_zero
    (L L' : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b' : ℕ) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (finiteConnectedSum L)
        (finiteConnectedSum (L' ++ List.replicate b' Z))).toClosedOrientedManifold
      (finiteConnectedSum ((L ++ L') ++ List.replicate b' Z)).toClosedOrientedManifold) := by
  simpa using orientedDiffeomorph_connectedSum_finiteConnectedSum_merge L L' Z 0 b'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_zero ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_zero

def mergePresentations :
    List (List (ConnectedClosedOrientedManifold.{u} 3) × ℕ) →
      List (ConnectedClosedOrientedManifold.{u} 3) × ℕ
  | [] => ([], 0)
  | p :: t => (p.1 ++ (mergePresentations t).1, p.2 + (mergePresentations t).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mergePresentations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mergePresentations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mergePresentations ``Submission.DifferentialGeometry.Topology.mergePresentations

theorem orientedDiffeomorph_finiteConnectedSum_mergePresentations
    (P : List (List (ConnectedClosedOrientedManifold.{u} 3) × ℕ))
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum
        (P.map fun p => finiteConnectedSum (p.1 ++ List.replicate p.2 Z))).toClosedOrientedManifold
      (finiteConnectedSum
        ((mergePresentations P).1 ++
          List.replicate (mergePresentations P).2 Z)).toClosedOrientedManifold) := by
  induction P with
  | nil =>
    simp only [List.map_nil, finiteConnectedSum_nil, mergePresentations, List.nil_append,
      List.replicate_zero]
    exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  | cons p t ih =>
    cases t with
    | nil =>
      simp only [List.map_cons, List.map_nil, mergePresentations, List.append_nil,
        finiteConnectedSum_singleton]
      exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
    | cons q u =>
      obtain ⟨e⟩ := ih
      obtain ⟨e'⟩ := nonempty_orientedDiffeomorph_connectedSum_right
        (X := finiteConnectedSum (p.1 ++ List.replicate p.2 Z)) ⟨e⟩
      obtain ⟨e''⟩ := orientedDiffeomorph_connectedSum_finiteConnectedSum_merge
        p.1 (mergePresentations (q :: u)).1 Z p.2 (mergePresentations (q :: u)).2
      exact ⟨e'.trans e''⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_mergePresentations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_mergePresentations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_mergePresentations ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_mergePresentations

theorem length_append_replicate_add (L L' : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b b' : ℕ) :
    ((L ++ L') ++ List.replicate (b + b') Z).length =
      (L ++ List.replicate b Z).length + (L' ++ List.replicate b' Z).length := by
  simp only [List.length_append, List.length_replicate]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.length_append_replicate_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.length_append_replicate_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.length_append_replicate_add ``Submission.DifferentialGeometry.Topology.length_append_replicate_add

theorem length_append_replicate_succ (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b : ℕ) :
    (L ++ List.replicate (b + 1) Z).length = (L ++ List.replicate b Z).length + 1 := by
  simp only [List.length_append, List.length_replicate]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.length_append_replicate_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.length_append_replicate_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.length_append_replicate_succ ``Submission.DifferentialGeometry.Topology.length_append_replicate_succ

theorem mergePresentations_exponent
    (P : List (List (ConnectedClosedOrientedManifold.{u} 3) × ℕ)) :
    (mergePresentations P).2 = (P.map fun p => p.2).sum := by
  induction P with
  | nil => rfl
  | cons p t ih => simp only [mergePresentations, List.map_cons, List.sum_cons, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mergePresentations_exponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mergePresentations_exponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mergePresentations_exponent ``Submission.DifferentialGeometry.Topology.mergePresentations_exponent

theorem mergePresentations_length (P : List (List (ConnectedClosedOrientedManifold.{u} 3) × ℕ)) :
    (mergePresentations P).1.length = (P.map fun p => p.1.length).sum := by
  induction P with
  | nil => rfl
  | cons p t ih =>
    simp only [mergePresentations, List.map_cons, List.sum_cons, ih, List.length_append]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mergePresentations_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mergePresentations_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mergePresentations_length ``Submission.DifferentialGeometry.Topology.mergePresentations_length

end DifferentialGeometry.Topology
