import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentPieceGluing

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

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S2 × Set.Icc (-2 : ℝ) 2

local instance partialGraphClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.partialGraphClosedCellCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.partialGraphClosedCellCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.partialGraphClosedCellCharted ``Submission.DifferentialGeometry.Topology.partialGraphClosedCellCharted
local instance partialGraphClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.partialGraphClosedCellIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.partialGraphClosedCellIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.partialGraphClosedCellIsManifold ``Submission.DifferentialGeometry.Topology.partialGraphClosedCellIsManifold

structure MarkedBall (N : ClosedOrientedManifold.{u} 3) where
  ball : ClosedCell 3 → N.Carrier
  ball_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball
  collar : Set N.Carrier
  collar_isOpen : IsOpen collar
  ball_subset_collar : _root_.Set.range ball ⊆ collar
  collarBudget : ℝ
  collarBudget_pos : 0 < collarBudget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall ``Submission.DifferentialGeometry.Topology.MarkedBall

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

def boundary (B : MarkedBall N) : S2 → N.Carrier := B.ball ∘ sphereToClosedCell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.boundary ``Submission.DifferentialGeometry.Topology.MarkedBall.boundary

theorem boundary_mem_collar (B : MarkedBall N) (z : S2) : B.boundary z ∈ B.collar :=
  B.ball_subset_collar (_root_.Set.mem_range_self (sphereToClosedCell z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.boundary_mem_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.boundary_mem_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.boundary_mem_collar ``Submission.DifferentialGeometry.Topology.MarkedBall.boundary_mem_collar

theorem collarBudget_ne_zero (B : MarkedBall N) : B.collarBudget ≠ 0 :=
  ne_of_gt B.collarBudget_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.collarBudget_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.collarBudget_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.collarBudget_ne_zero ``Submission.DifferentialGeometry.Topology.MarkedBall.collarBudget_ne_zero

end MarkedBall

structure MarkedManifoldGraph where
  Vertex : Type u
  Edge : Type u
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  edgeDecidableEq : DecidableEq Edge
  endpoint : Edge → Bool → Vertex
  vertexManifold : Vertex → ConnectedClosedOrientedManifold.{u} 3
  flag : (e : Edge) → (b : Bool) →
    MarkedBall (vertexManifold (endpoint e b)).toClosedOrientedManifold
  flag_collar_disjoint : ∀ (v : Vertex)
      (f f' : {p : Edge × Bool // endpoint p.1 p.2 = v}), f ≠ f' →
      Disjoint (f.2 ▸ (flag f.1.1 f.1.2).collar) (f'.2 ▸ (flag f'.1.1 f'.1.2).collar)
  attach : (e : Edge) → (b : Bool) → S2 → (vertexManifold (endpoint e b)).Carrier
  attach_eq : ∀ (e : Edge) (b : Bool) (z : S2),
    attach e b z = (flag e b).ball (sphereToClosedCell z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph

attribute [instance] MarkedManifoldGraph.vertexFintype MarkedManifoldGraph.edgeFintype
  MarkedManifoldGraph.edgeDecidableEq

private theorem reachable_sup_edge_of_walk {V : Type u} {H : SimpleGraph V} {a b : V} :
    ∀ {u v : V}, (H ⊔ SimpleGraph.edge a b).Walk u v →
      H.Reachable u v ∨ (H.Reachable u a ∧ H.Reachable v b) ∨
        (H.Reachable u b ∧ H.Reachable v a)
  | _, _, .nil => Or.inl (SimpleGraph.Reachable.refl _)
  | _, _, .cons hadj p => by
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hadj
    have ih := reachable_sup_edge_of_walk p
    rcases hadj with hadj | ⟨hmem, _⟩
    · have huw : H.Reachable _ _ := hadj.reachable
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (huw.trans h)
      · exact Or.inr (Or.inl ⟨huw.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨huw.trans h1, h2⟩)
    · rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h.symm⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2⟩)
        · exact Or.inl h2.symm
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h.symm⟩)
        · exact Or.inl h2.symm
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h2⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.reachable_sup_edge_of_walk
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.reachable_sup_edge_of_walk target :: scope.openDecls } }

private theorem connectedComponents_mk_eq_of_preconnectedSpace {α : Type u} [TopologicalSpace α]
    (h : PreconnectedSpace α) (x y : α) : ConnectedComponents.mk x = ConnectedComponents.mk y :=
  @Subsingleton.elim _ (@ConnectedComponents.subsingleton α inferInstance h) x y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.connectedComponents_mk_eq_of_preconnectedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.connectedComponents_mk_eq_of_preconnectedSpace target :: scope.openDecls } }

theorem reachable_sup_edge_iff {V : Type u} (H : SimpleGraph V) (a b u v : V) :
    (H ⊔ SimpleGraph.edge a b).Reachable u v ↔
      H.Reachable u v ∨ (H.Reachable u a ∧ H.Reachable v b) ∨
        (H.Reachable u b ∧ H.Reachable v a) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p⟩ := h
    exact reachable_sup_edge_of_walk p
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono le_sup_left
    · by_cases hab : a = b
      · subst hab
        exact (h1.mono le_sup_left).trans (h2.mono le_sup_left).symm
      · refine (h1.mono le_sup_left).trans ((SimpleGraph.Adj.reachable ?_).trans
          (h2.mono le_sup_left).symm)
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
    · by_cases hab : a = b
      · subst hab
        exact (h1.mono le_sup_left).trans (h2.mono le_sup_left).symm
      · refine (h1.mono le_sup_left).trans ((SimpleGraph.Adj.reachable ?_).trans
          (h2.mono le_sup_left).symm)
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reachable_sup_edge_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reachable_sup_edge_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reachable_sup_edge_iff ``Submission.DifferentialGeometry.Topology.reachable_sup_edge_iff

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

def source (e : G.Edge) : G.Vertex := G.endpoint e _root_.Bool.false

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.source ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.source

def target (e : G.Edge) : G.Vertex := G.endpoint e _root_.Bool.true

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.target ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.target

def removedBallSet (S : Finset G.Edge) (v : G.Vertex) : Set (G.vertexManifold v).Carrier :=
  {x | ∃ (e : G.Edge) (_ : e ∈ S) (b : Bool) (h : G.endpoint e b = v),
    x ∈ h ▸ (_root_.Set.range (G.flag e b).ball \
      _root_.Set.range ((G.flag e b).ball ∘ sphereToClosedCell))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet

abbrev puncturedCarrier (S : Finset G.Edge) (v : G.Vertex) : Type u :=
  {x : (G.vertexManifold v).Carrier // x ∉ G.removedBallSet S v}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.puncturedCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.puncturedCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.puncturedCarrier ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.puncturedCarrier

abbrev cylinderCarrier (_ : G.Edge) : Type := Tube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.cylinderCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.cylinderCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.cylinderCarrier ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.cylinderCarrier

def gluedEdges (S : Finset G.Edge) : Finset G.Edge := S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.gluedEdges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.gluedEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.gluedEdges ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.gluedEdges

def remainingEdges (S : Finset G.Edge) : Finset G.Edge := Sᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges

theorem mem_gluedEdges (S : Finset G.Edge) (e : G.Edge) : e ∈ G.gluedEdges S ↔ e ∈ S :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_gluedEdges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_gluedEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_gluedEdges ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_gluedEdges

theorem mem_remainingEdges (S : Finset G.Edge) (e : G.Edge) :
    e ∈ G.remainingEdges S ↔ e ∉ S := Finset.mem_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges

theorem remainingEdges_insert (S : Finset G.Edge) (e : G.Edge) :
    G.remainingEdges (_root_.Insert.insert e S) = (G.remainingEdges S).erase e := by
  ext f
  simp only [remainingEdges, Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.remainingEdges_insert

theorem mem_remainingEdges_insert (S : Finset G.Edge) (e f : G.Edge) :
    f ∈ G.remainingEdges (_root_.Insert.insert e S) ↔ f ≠ e ∧ f ∈ G.remainingEdges S := by
  rw [remainingEdges_insert, Finset.mem_erase]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_remainingEdges_insert

def processedGraph (S : Finset G.Edge) : SimpleGraph G.Vertex :=
  S.sup fun e => SimpleGraph.edge (G.source e) (G.target e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph

theorem processedGraph_insert (S : Finset G.Edge) (e : G.Edge) :
    G.processedGraph (_root_.Insert.insert e S) =
      SimpleGraph.edge (G.source e) (G.target e) ⊔ G.processedGraph S :=
  Finset.sup_insert

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_insert

theorem processedGraph_mono {S T : Finset G.Edge} (h : S ⊆ T) :
    G.processedGraph S ≤ G.processedGraph T := by
  rw [processedGraph, processedGraph]
  refine Finset.sup_le fun e he => ?_
  exact Finset.le_sup (f := fun e => SimpleGraph.edge (G.source e) (G.target e)) (h he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_mono ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_mono

theorem processedGraph_reachable_insert (S : Finset G.Edge) (e : G.Edge) (u v : G.Vertex) :
    (G.processedGraph (_root_.Insert.insert e S)).Reachable u v ↔
      (G.processedGraph S).Reachable u v ∨
        ((G.processedGraph S).Reachable u (G.source e) ∧
          (G.processedGraph S).Reachable v (G.target e)) ∨
        ((G.processedGraph S).Reachable u (G.target e) ∧
          (G.processedGraph S).Reachable v (G.source e)) := by
  rw [G.processedGraph_insert S e, sup_comm]
  exact reachable_sup_edge_iff (G.processedGraph S) (G.source e) (G.target e) u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_reachable_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_reachable_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_reachable_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_reachable_insert

theorem reachable_source_target_insert (S : Finset G.Edge) (e : G.Edge) :
    (G.processedGraph (_root_.Insert.insert e S)).Reachable (G.source e) (G.target e) :=
  (G.processedGraph_reachable_insert S e _ _).mpr
    (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_source_target_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_source_target_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_source_target_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_source_target_insert

theorem not_reachable_insert_of_not_reachable (S : Finset G.Edge) (e : G.Edge) {u v : G.Vertex}
    (huv : ¬ (G.processedGraph S).Reachable u v)
    (h1 : ¬ (G.processedGraph S).Reachable u (G.source e))
    (h2 : ¬ (G.processedGraph S).Reachable u (G.target e)) :
    ¬ (G.processedGraph (_root_.Insert.insert e S)).Reachable u v := by
  rw [G.processedGraph_reachable_insert S e]
  rintro (h | ⟨h1', -⟩ | ⟨h1', -⟩)
  exacts [huv h, h1 h1', h2 h1']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_insert_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_insert_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_insert_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_insert_of_not_reachable

abbrev twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) : MarkedManifoldGraph.{0} where
  Vertex := Bool
  Edge := PUnit
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun _ b => b
  vertexManifold := fun _ => N
  flag := fun _ b => if b then B' else B
  flag_collar_disjoint := fun v f f' hne => by
    refine absurd (Subtype.ext ?_) hne
    refine Prod.ext (Subsingleton.elim _ _) ?_
    exact f.2.trans f'.2.symm
  attach := fun _ b => (if b then B' else B).ball ∘ sphereToClosedCell
  attach_eq := fun _ _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertex

theorem processedGraph_empty_twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    (twoVertex N B B').processedGraph (∅ : Finset PUnit) = ⊥ :=
  Finset.sup_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_empty_twoVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_empty_twoVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_empty_twoVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.processedGraph_empty_twoVertex

theorem not_reachable_twoVertex_empty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    ¬ ((twoVertex N B B').processedGraph ∅).Reachable _root_.Bool.false true := by
  rw [processedGraph_empty_twoVertex, SimpleGraph.reachable_bot]
  exact Bool.false_ne_true

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertex_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertex_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertex_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertex_empty

theorem reachable_twoVertex_insert (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    ((twoVertex N B B').processedGraph
      (_root_.Insert.insert PUnit.unit (∅ : Finset PUnit))).Reachable _root_.Bool.false true :=
  (twoVertex N B B').reachable_source_target_insert ∅ PUnit.unit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_twoVertex_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_twoVertex_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_twoVertex_insert ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.reachable_twoVertex_insert

end MarkedManifoldGraph

structure PartialRealization (G : MarkedManifoldGraph.{u}) (S : Finset G.Edge) where
  realization : ClosedOrientedManifold.{u} 3
  vertexPiece : (v : G.Vertex) → C(G.puncturedCarrier S v, realization.Carrier)
  cylinderPiece : (e : G.Edge) → e ∈ S → C(G.cylinderCarrier e, realization.Carrier)
  survivingFlag : (e : G.Edge) → e ∉ S → MarkedBall realization
  covers : ∀ x : realization.Carrier,
    (∃ (v : G.Vertex) (y : G.puncturedCarrier S v), vertexPiece v y = x) ∨
    (∃ (e : G.Edge) (he : e ∈ S) (y : G.cylinderCarrier e), cylinderPiece e he y = x)
  survivingFlag_collar_disjoint : ∀ (e e' : G.Edge) (he : e ∉ S) (he' : e' ∉ S), e ≠ e' →
    Disjoint (survivingFlag e he).collar (survivingFlag e' he').collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization ``Submission.DifferentialGeometry.Topology.PartialRealization

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} (P : PartialRealization G S)

def collarBudget (e : G.Edge) (he : e ∉ S) : ℝ := (P.survivingFlag e he).collarBudget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.collarBudget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.collarBudget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.collarBudget ``Submission.DifferentialGeometry.Topology.PartialRealization.collarBudget

theorem collarBudget_pos (e : G.Edge) (he : e ∉ S) : 0 < P.collarBudget e he :=
  (P.survivingFlag e he).collarBudget_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.collarBudget_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.collarBudget_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.collarBudget_pos ``Submission.DifferentialGeometry.Topology.PartialRealization.collarBudget_pos

def survivingFlags (e : {e : G.Edge // e ∉ S}) : MarkedBall P.realization :=
  P.survivingFlag e.1 e.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.survivingFlags then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.survivingFlags"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.survivingFlags ``Submission.DifferentialGeometry.Topology.PartialRealization.survivingFlags

def assignedToProcessedComponents : Prop :=
  ∀ (v v' : G.Vertex) (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v'),
    P.vertexPiece v y = P.vertexPiece v' y' → (G.processedGraph S).Reachable v v'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents ``Submission.DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents

def componentCorrespondence : Prop :=
  ∀ (v v' : G.Vertex) (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v'),
    ConnectedComponents.mk (P.vertexPiece v y) = ConnectedComponents.mk (P.vertexPiece v' y') ↔
      (G.processedGraph S).Reachable v v'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.componentCorrespondence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence ``Submission.DifferentialGeometry.Topology.PartialRealization.componentCorrespondence

theorem assignedToProcessedComponents_of_componentCorrespondence (h : P.componentCorrespondence) :
    P.assignedToProcessedComponents :=
  fun v v' y y' hv => (h v v' y y').mp (by simpa using congrArg ConnectedComponents.mk hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents_of_componentCorrespondence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents_of_componentCorrespondence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents_of_componentCorrespondence ``Submission.DifferentialGeometry.Topology.PartialRealization.assignedToProcessedComponents_of_componentCorrespondence

theorem component_eq_of_reachable (h : P.componentCorrespondence) {v v' : G.Vertex}
    (hv : (G.processedGraph S).Reachable v v')
    (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v') :
    ConnectedComponents.mk (P.vertexPiece v y) = ConnectedComponents.mk (P.vertexPiece v' y') :=
  (h v v' y y').mpr hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.component_eq_of_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.component_eq_of_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.component_eq_of_reachable ``Submission.DifferentialGeometry.Topology.PartialRealization.component_eq_of_reachable

theorem component_eq_source_target_insert (e : G.Edge)
    (P : PartialRealization G (_root_.Insert.insert e S)) (h : P.componentCorrespondence)
    (y : G.puncturedCarrier (_root_.Insert.insert e S) (G.source e))
    (y' : G.puncturedCarrier (_root_.Insert.insert e S) (G.target e)) :
    ConnectedComponents.mk (P.vertexPiece (G.source e) y) =
      ConnectedComponents.mk (P.vertexPiece (G.target e) y') :=
  P.component_eq_of_reachable h (G.reachable_source_target_insert S e) y y'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.component_eq_source_target_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.component_eq_source_target_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.component_eq_source_target_insert ``Submission.DifferentialGeometry.Topology.PartialRealization.component_eq_source_target_insert

def IsConnectedSumPresentable (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  ∃ b : ℕ, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
    (finiteConnectedSum (Vlist ++ List.replicate b Z)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.IsConnectedSumPresentable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.IsConnectedSumPresentable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.IsConnectedSumPresentable ``Submission.DifferentialGeometry.Topology.PartialRealization.IsConnectedSumPresentable

def IsPartialInvariant (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  P.IsConnectedSumPresentable Z Vlist ∧ P.componentCorrespondence

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.IsPartialInvariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.IsPartialInvariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.IsPartialInvariant ``Submission.DifferentialGeometry.Topology.PartialRealization.IsPartialInvariant

end PartialRealization

namespace MarkedManifoldGraph

abbrev oneVertex (N : ConnectedClosedOrientedManifold.{u} 3) : MarkedManifoldGraph.{u} where
  Vertex := PUnit
  Edge := PEmpty.{u + 1}
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun e => PEmpty.elim e
  vertexManifold := fun _ => N
  flag := fun e => PEmpty.elim e
  flag_collar_disjoint := fun _ f => PEmpty.elim f.1.1
  attach := fun e => PEmpty.elim e
  attach_eq := fun e => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertex

end MarkedManifoldGraph

namespace PartialRealization

def oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    PartialRealization (MarkedManifoldGraph.oneVertex N) ∅ where
  realization := N.toClosedOrientedManifold
  vertexPiece := fun _ => ⟨Subtype.val, continuous_subtype_val⟩
  cylinderPiece := fun e => PEmpty.elim e
  survivingFlag := fun e => PEmpty.elim e
  covers := fun x =>
    Or.inl ⟨PUnit.unit, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩
  survivingFlag_collar_disjoint := fun e => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.oneVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.oneVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.oneVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.oneVertexEmpty

theorem componentCorrespondence_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    (oneVertexEmpty N).componentCorrespondence := by
  have hpre : PreconnectedSpace (oneVertexEmpty N).realization.Carrier :=
    inferInstanceAs (PreconnectedSpace N.Carrier)
  intro v v' y y'
  constructor
  · intro _
    exact SimpleGraph.Reachable.refl v
  · intro _
    exact connectedComponents_mk_eq_of_preconnectedSpace hpre _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_oneVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_oneVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_oneVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.componentCorrespondence_oneVertexEmpty

theorem nonempty_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (PartialRealization (MarkedManifoldGraph.oneVertex N) ∅) :=
  ⟨oneVertexEmpty N⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.nonempty_oneVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.nonempty_oneVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.nonempty_oneVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.nonempty_oneVertexEmpty

theorem remainingEdges_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    (MarkedManifoldGraph.oneVertex N).remainingEdges (∅ : Finset PEmpty.{u + 1}) = ∅ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.remainingEdges_oneVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.remainingEdges_oneVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.remainingEdges_oneVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.remainingEdges_oneVertexEmpty

theorem orientedDiffeomorph_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (oneVertexEmpty N).realization
      (finiteConnectedSum [N]).toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.orientedDiffeomorph_oneVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.orientedDiffeomorph_oneVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.orientedDiffeomorph_oneVertexEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.orientedDiffeomorph_oneVertexEmpty

end PartialRealization

structure PartialStepLaw (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop where
  initial : ∃ P : PartialRealization G ∅, P.IsPartialInvariant Z Vlist
  step : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsPartialInvariant Z Vlist →
      ∃ P' : PartialRealization G (_root_.Insert.insert e S), P'.IsPartialInvariant Z Vlist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialStepLaw ``Submission.DifferentialGeometry.Topology.PartialStepLaw

theorem exists_invariant_of_stepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    {Vlist : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : PartialStepLaw G Z Vlist) (S : Finset G.Edge) :
    ∃ P : PartialRealization G S, P.IsPartialInvariant Z Vlist := by
  induction S using Finset.induction_on with
  | empty => exact h.initial
  | insert e S he ih =>
    obtain ⟨P, hP⟩ := ih
    exact h.step S P e he hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_invariant_of_stepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_invariant_of_stepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_invariant_of_stepLaw ``Submission.DifferentialGeometry.Topology.exists_invariant_of_stepLaw

theorem exists_connectedSumPresentation_full_of_stepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    {Vlist : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : PartialStepLaw G Z Vlist) :
    ∃ (P : PartialRealization G Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum (Vlist ++ List.replicate b Z)).toClosedOrientedManifold) := by
  obtain ⟨P, hpres, -⟩ := exists_invariant_of_stepLaw h Finset.univ
  exact ⟨P, hpres⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_connectedSumPresentation_full_of_stepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_connectedSumPresentation_full_of_stepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_connectedSumPresentation_full_of_stepLaw ``Submission.DifferentialGeometry.Topology.exists_connectedSumPresentation_full_of_stepLaw

theorem oneVertexStepLaw (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    PartialStepLaw (MarkedManifoldGraph.oneVertex N) Z [N] where
  initial := ⟨PartialRealization.oneVertexEmpty N,
    ⟨0, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩,
    PartialRealization.componentCorrespondence_oneVertexEmpty N⟩
  step := fun _ _ e _ _ => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.oneVertexStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.oneVertexStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.oneVertexStepLaw ``Submission.DifferentialGeometry.Topology.oneVertexStepLaw

theorem exists_connectedSumPresentation_oneVertex_of_stepLaw
    (N Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ (P : PartialRealization (MarkedManifoldGraph.oneVertex N) Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum ([N] ++ List.replicate b Z)).toClosedOrientedManifold) :=
  exists_connectedSumPresentation_full_of_stepLaw (oneVertexStepLaw N Z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_connectedSumPresentation_oneVertex_of_stepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_connectedSumPresentation_oneVertex_of_stepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_connectedSumPresentation_oneVertex_of_stepLaw ``Submission.DifferentialGeometry.Topology.exists_connectedSumPresentation_oneVertex_of_stepLaw

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

def ComponentPresentationData (E : SphericalCutCapTransition M Q)
    (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
    ∃ (L : List (ConnectedClosedOrientedManifold.{u} 3)) (b : ℕ),
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
          B.toClosedOrientedManifold)) L (E.cappedCutPieceFactorList C) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ List.replicate b S)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.ComponentPresentationData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.ComponentPresentationData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.ComponentPresentationData ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ComponentPresentationData

theorem componentPresentationData_of_cutComponentPieceDistinctGluing
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutComponentPieceDistinctGluing S) : E.ComponentPresentationData S := by
  intro C hC
  obtain ⟨b, hb⟩ := h C hC
  exact ⟨E.cappedCutPieceFactorList C, b, List.forall₂_same.mpr fun A _ =>
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl A.toClosedOrientedManifold⟩, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_cutComponentPieceDistinctGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_cutComponentPieceDistinctGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_cutComponentPieceDistinctGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_cutComponentPieceDistinctGluing

theorem cutComponentPieceDistinctGluing_of_componentPresentationData
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.ComponentPresentationData S) : E.cutComponentPieceDistinctGluing S := by
  intro C hC
  obtain ⟨L, b, hL, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := finiteConnectedSum_congr
    (List.rel_append hL (List.forall₂_same.mpr fun A _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl A.toClosedOrientedManifold⟩))
  exact ⟨b, ⟨ρ.trans σ⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentPieceDistinctGluing_of_componentPresentationData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentPieceDistinctGluing_of_componentPresentationData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentPieceDistinctGluing_of_componentPresentationData ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentPieceDistinctGluing_of_componentPresentationData

theorem sphericalSummandCompletion_of_componentPresentationData
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.ComponentPresentationData S) : E.sphericalSummandCompletion S :=
  (E.cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion S).mp
    (E.cutComponentPieceDistinctGluing_of_componentPresentationData S h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_componentPresentationData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_componentPresentationData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_componentPresentationData ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_componentPresentationData

theorem componentPresentationData_iff_cutComponentPieceDistinctGluing
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.ComponentPresentationData S ↔ E.cutComponentPieceDistinctGluing S :=
  ⟨E.cutComponentPieceDistinctGluing_of_componentPresentationData S,
    E.componentPresentationData_of_cutComponentPieceDistinctGluing S⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_cutComponentPieceDistinctGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_cutComponentPieceDistinctGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_cutComponentPieceDistinctGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_cutComponentPieceDistinctGluing

theorem componentPresentationData_of_forall_cutIndices_eq_empty
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.ComponentPresentationData S :=
  E.componentPresentationData_of_cutComponentPieceDistinctGluing S
    ((E.cutComponentPieceGluing_iff_cutComponentPieceDistinctGluing S
        fun C => E.injective_cappedFactor_of_cutIndices_eq_empty C (h C)).mp
      (E.cutComponentPieceGluing_of_forall_cutIndices_eq_empty S h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_of_forall_cutIndices_eq_empty

theorem componentPresentationData_iff_sphericalSummandCompletion
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.ComponentPresentationData S ↔ E.sphericalSummandCompletion S :=
  (E.componentPresentationData_iff_cutComponentPieceDistinctGluing S).trans
    (E.cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_sphericalSummandCompletion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_sphericalSummandCompletion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_sphericalSummandCompletion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentPresentationData_iff_sphericalSummandCompletion

end SphericalCutCapTransition

end DifferentialGeometry.Topology
