import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationAnalytic
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteCongruence
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

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

def vertexBlock (S : Finset G.Edge) (v : G.Vertex) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v' => (G.processedGraph S).Reachable v v'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock

def vertexBlockList (S : Finset G.Edge) (v : G.Vertex) :
    List (ConnectedClosedOrientedManifold.{u} 3) :=
  (G.vertexBlock S v).toList.map G.vertexManifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList

theorem vertexBlockList_eq (S : Finset G.Edge) (v : G.Vertex) :
    G.vertexBlockList S v = (G.vertexBlock S v).toList.map G.vertexManifold := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq

theorem mem_vertexBlock (S : Finset G.Edge) (v v' : G.Vertex) :
    v' ∈ G.vertexBlock S v ↔ (G.processedGraph S).Reachable v v' := by
  classical
  simp only [vertexBlock, Finset.mem_filter, Finset.mem_univ, true_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_vertexBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_vertexBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_vertexBlock ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_vertexBlock

theorem vertexBlock_eq_univ_of_preconnected (S : Finset G.Edge) (v : G.Vertex)
    (h : (G.processedGraph S).Preconnected) : G.vertexBlock S v = Finset.univ := by
  ext v'
  rw [mem_vertexBlock]
  exact ⟨fun _ => Finset.mem_univ v', fun _ => h v v'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_univ_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_univ_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_univ_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_eq_univ_of_preconnected

theorem vertexBlockList_eq_univ_toList_of_preconnected (S : Finset G.Edge) (v : G.Vertex)
    (h : (G.processedGraph S).Preconnected) :
    G.vertexBlockList S v =
      (Finset.univ : Finset G.Vertex).toList.map G.vertexManifold := by
  rw [vertexBlockList, vertexBlock_eq_univ_of_preconnected G S v h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq_univ_toList_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq_univ_toList_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq_univ_toList_of_preconnected ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_eq_univ_toList_of_preconnected

theorem vertexBlock_empty (v : G.Vertex) : G.vertexBlock ∅ v = {v} := by
  ext v'
  rw [mem_vertexBlock, show G.processedGraph ∅ = (⊥ : SimpleGraph G.Vertex) from
    Finset.sup_empty, SimpleGraph.reachable_bot, Finset.mem_singleton]
  exact eq_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_empty

theorem vertexBlockList_empty (v : G.Vertex) :
    G.vertexBlockList ∅ v = [G.vertexManifold v] := by
  rw [vertexBlockList, vertexBlock_empty, Finset.toList_singleton, List.map_cons, List.map_nil]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_empty

theorem vertexBlock_insert_of_reachable (S : Finset G.Edge) (e : G.Edge)
    (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex) :
    G.vertexBlock (_root_.Insert.insert e S) v = G.vertexBlock S v := by
  ext v'
  rw [mem_vertexBlock, mem_vertexBlock, G.processedGraph_reachable_insert]
  constructor
  · rintro (h' | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact h'
    · exact h₁.trans (h.trans h₂.symm)
    · exact h₁.trans (h.symm.trans h₂.symm)
  · exact fun h' => Or.inl h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_reachable

theorem vertexBlockList_insert_of_reachable (S : Finset G.Edge) (e : G.Edge)
    (h : (G.processedGraph S).Reachable (G.source e) (G.target e)) (v : G.Vertex) :
    G.vertexBlockList (_root_.Insert.insert e S) v = G.vertexBlockList S v := by
  rw [vertexBlockList, vertexBlockList, vertexBlock_insert_of_reachable G S e h v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_reachable

theorem vertexBlock_insert_of_not_reachable [DecidableEq G.Vertex] (S : Finset G.Edge)
    (e : G.Edge) (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) :
    G.vertexBlock (_root_.Insert.insert e S) (G.source e) =
      G.vertexBlock S (G.source e) ∪ G.vertexBlock S (G.target e) := by
  ext v'
  rw [mem_vertexBlock, Finset.mem_union, mem_vertexBlock, mem_vertexBlock,
    G.processedGraph_reachable_insert]
  constructor
  · rintro (h' | ⟨-, h₂⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl h'
    · exact Or.inr h₂.symm
    · exact absurd h₁ h
  · rintro (h' | h')
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h'.symm⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlock_insert_of_not_reachable

theorem disjoint_vertexBlock_of_not_reachable (S : Finset G.Edge) (e : G.Edge)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) :
    Disjoint (G.vertexBlock S (G.source e)) (G.vertexBlock S (G.target e)) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact h (((mem_vertexBlock G S (G.source e) v).mp hv).trans
    (((mem_vertexBlock G S (G.target e) v).mp hv').symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_vertexBlock_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_vertexBlock_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_vertexBlock_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_vertexBlock_of_not_reachable

theorem vertexBlockList_insert_of_not_reachable (S : Finset G.Edge) (e : G.Edge)
    (h : ¬ (G.processedGraph S).Reachable (G.source e) (G.target e)) :
    List.Perm (G.vertexBlockList (_root_.Insert.insert e S) (G.source e))
      (G.vertexBlockList S (G.source e) ++ G.vertexBlockList S (G.target e)) := by
  classical
  have huni : G.vertexBlock (_root_.Insert.insert e S) (G.source e) =
      G.vertexBlock S (G.source e) ∪ G.vertexBlock S (G.target e) :=
    vertexBlock_insert_of_not_reachable G S e h
  have hperm : List.Perm
      ((G.vertexBlock S (G.source e) ∪ G.vertexBlock S (G.target e)).toList)
      ((G.vertexBlock S (G.source e)).toList ++ (G.vertexBlock S (G.target e)).toList) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).mpr fun a => ?_
    · refine List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) ?_
      rw [List.disjoint_left]
      intro a ha ha'
      exact (Finset.disjoint_left.mp
        (disjoint_vertexBlock_of_not_reachable G S e h)) (Finset.mem_toList.mp ha)
        (Finset.mem_toList.mp ha')
    · simp only [Finset.mem_toList, Finset.mem_union, List.mem_append]
  rw [vertexBlockList, huni, vertexBlockList, vertexBlockList]
  simpa using hperm.map G.vertexManifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_not_reachable ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_insert_of_not_reachable

theorem removedBallSet_eq_empty_of_not_endpoint (S : Finset G.Edge) (v : G.Vertex)
    (h : ∀ (e : G.Edge) (b : Bool), G.endpoint e b ≠ v) : G.removedBallSet S v = ∅ := by
  ext x
  constructor
  · rintro ⟨e, -, b, hv, -⟩
    exact (h e b) hv
  · intro hx
    exact (Set.notMem_empty x hx).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_eq_empty_of_not_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_eq_empty_of_not_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_eq_empty_of_not_endpoint ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_eq_empty_of_not_endpoint

theorem removedBallSet_empty (v : G.Vertex) : G.removedBallSet ∅ v = ∅ := by
  ext x
  constructor
  · rintro ⟨e, he, -, -, -⟩
    exact (Finset.notMem_empty e he).elim
  · intro hx
    exact (Set.notMem_empty x hx).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.removedBallSet_empty

theorem nonempty_puncturedCarrier (S : Finset G.Edge) (v : G.Vertex) :
    Nonempty (G.puncturedCarrier S v) := by
  classical
  by_cases h : ∃ (e : G.Edge) (b : Bool), G.endpoint e b = v
  · obtain ⟨e, b, hv⟩ := h
    exact ⟨hv ▸ G.flagBoundaryPoint S e b sphereBasePoint⟩
  · refine ⟨⟨Classical.choice (inferInstance : Nonempty (G.vertexManifold v).Carrier), ?_⟩⟩
    rw [removedBallSet_eq_empty_of_not_endpoint G S v fun e b hv => h ⟨e, b, hv⟩]
    exact Set.notMem_empty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_puncturedCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_puncturedCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_puncturedCarrier ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_puncturedCarrier

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge}

theorem preconnectedSpace_of_isConnectedSumPresentable (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : P.IsConnectedSumPresentable Z Vlist) : PreconnectedSpace P.realization.Carrier := by
  obtain ⟨b, ⟨ρ⟩⟩ := h
  have hcs : ConnectedSpace P.realization.Carrier :=
    (ρ.1.toHomeomorph.connectedSpace_iff).mpr inferInstance
  exact hcs.toPreconnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.preconnectedSpace_of_isConnectedSumPresentable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.preconnectedSpace_of_isConnectedSumPresentable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.preconnectedSpace_of_isConnectedSumPresentable ``Submission.DifferentialGeometry.Topology.PartialRealization.preconnectedSpace_of_isConnectedSumPresentable

theorem not_isPartialInvariant_of_not_reachable (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) {v v' : G.Vertex}
    (hv : ¬ (G.processedGraph S).Reachable v v')
    (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v') :
    ¬ P.IsPartialInvariant Z Vlist := by
  rintro ⟨hpres, hcorr⟩
  have := preconnectedSpace_of_isConnectedSumPresentable P Z Vlist hpres
  exact hv ((hcorr v v' y y').mp (Subsingleton.elim _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.not_isPartialInvariant_of_not_reachable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.not_isPartialInvariant_of_not_reachable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.not_isPartialInvariant_of_not_reachable ``Submission.DifferentialGeometry.Topology.PartialRealization.not_isPartialInvariant_of_not_reachable

def HasBlockPresentation (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ b : G.Vertex → ℕ,
    (∀ v v' : G.Vertex, (G.processedGraph S).Reachable v v' → b v = b v') ∧
    ∀ (v : G.Vertex) (y : G.puncturedCarrier S v),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (P.realization.component
          (ConnectedComponents.mk (P.vertexPiece v y))).toClosedOrientedManifold
        (finiteConnectedSum
          (G.vertexBlockList S v ++ List.replicate (b v) Z)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.HasBlockPresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.HasBlockPresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.HasBlockPresentation ``Submission.DifferentialGeometry.Topology.PartialRealization.HasBlockPresentation

def CylinderComponentCovering (P : PartialRealization G S) : Prop :=
  ∀ x : P.realization.Carrier, ∃ (v : G.Vertex) (y : G.puncturedCarrier S v),
    ConnectedComponents.mk x = ConnectedComponents.mk (P.vertexPiece v y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.CylinderComponentCovering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.CylinderComponentCovering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.CylinderComponentCovering ``Submission.DifferentialGeometry.Topology.PartialRealization.CylinderComponentCovering

def IsBlockInvariant (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  P.componentCorrespondence ∧ P.HasBlockPresentation Z ∧ P.CylinderComponentCovering

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.IsBlockInvariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.IsBlockInvariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.IsBlockInvariant ``Submission.DifferentialGeometry.Topology.PartialRealization.IsBlockInvariant

end PartialRealization

structure BlockStepLaw (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop where
  initial : ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z
  step : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsBlockInvariant Z → ∃ P' : PartialRealization G (_root_.Insert.insert e S), P'.IsBlockInvariant Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BlockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BlockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BlockStepLaw ``Submission.DifferentialGeometry.Topology.BlockStepLaw

theorem exists_blockInvariant_of_stepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : BlockStepLaw G Z)
    (S : Finset G.Edge) : ∃ P : PartialRealization G S, P.IsBlockInvariant Z := by
  induction S using Finset.induction_on with
  | empty => exact h.initial
  | insert e S he ih =>
    obtain ⟨P, hP⟩ := ih
    exact h.step S P e he hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_blockInvariant_of_stepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_blockInvariant_of_stepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_blockInvariant_of_stepLaw ``Submission.DifferentialGeometry.Topology.exists_blockInvariant_of_stepLaw

theorem exists_connectedSumPresentation_of_blockStepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : BlockStepLaw G Z) (v₀ : G.Vertex)
    (hconn : (G.processedGraph Finset.univ).Preconnected) :
    ∃ (P : PartialRealization G Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum ((Finset.univ : Finset G.Vertex).toList.map G.vertexManifold ++
          List.replicate b Z)).toClosedOrientedManifold) := by
  obtain ⟨P, hcorr, hpres, hland⟩ := exists_blockInvariant_of_stepLaw h Finset.univ
  obtain ⟨b, -, hb⟩ := hpres
  have hpre : PreconnectedSpace P.realization.Carrier := by
    rw [preconnectedSpace_iff_connectedComponent]
    intro x
    rw [_root_.Set.eq_univ_iff_forall]
    intro z
    rw [← ConnectedComponents.coe_eq_coe']
    obtain ⟨v, y, hv⟩ := hland x
    obtain ⟨v', y', hv'⟩ := hland z
    rw [hv', hv]
    exact ((hcorr v v' y y').mpr (hconn v v')).symm
  have hbl :=
    MarkedManifoldGraph.vertexBlockList_eq_univ_toList_of_preconnected G Finset.univ v₀ hconn
  obtain ⟨y₀⟩ := MarkedManifoldGraph.nonempty_puncturedCarrier G Finset.univ v₀
  obtain ⟨ρ⟩ := hb v₀ y₀
  rw [hbl] at ρ
  exact ⟨P, b v₀, ⟨(ClosedOrientedManifold.componentOrientedDiffeomorph P.realization
    (ConnectedComponents.mk (P.vertexPiece v₀ y₀))).symm.trans ρ⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_connectedSumPresentation_of_blockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_connectedSumPresentation_of_blockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_connectedSumPresentation_of_blockStepLaw ``Submission.DifferentialGeometry.Topology.exists_connectedSumPresentation_of_blockStepLaw

theorem orientedDiffeomorph_connectedSum_finiteConnectedSum_append
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) :=
  (finiteConnectedSum_append L K).elim fun e => ⟨e.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_append then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_append"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_append ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_append

theorem orientedDiffeomorph_finiteConnectedSum_append_replicate
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b b' : ℕ) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ List.replicate (b + b') Z)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum (L ++ List.replicate b Z))
        (finiteConnectedSum (List.replicate b' Z))).toClosedOrientedManifold) := by
  rw [List.replicate_add, ← List.append_assoc]
  exact finiteConnectedSum_append (L ++ List.replicate b Z) (List.replicate b' Z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_append_replicate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_append_replicate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_append_replicate ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_finiteConnectedSum_append_replicate

theorem orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate_succ
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b : ℕ) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (finiteConnectedSum (L ++ List.replicate b Z)) Z).toClosedOrientedManifold
      (finiteConnectedSum (L ++ List.replicate (b + 1) Z)).toClosedOrientedManifold) := by
  rw [List.replicate_succ', ← List.append_assoc]
  obtain ⟨e⟩ := finiteConnectedSum_append (L ++ List.replicate b Z) [Z]
  exact ⟨by simpa only [finiteConnectedSum_singleton] using e.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate_succ ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_replicate_succ

theorem perm_append_comm_blocks (L L' : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b b' : ℕ) :
    List.Perm ((L ++ List.replicate b Z) ++ (L' ++ List.replicate b' Z))
      ((L ++ L') ++ List.replicate (b + b') Z) := by
  rw [List.replicate_add, List.append_assoc, List.append_assoc]
  exact List.Perm.append_left L
    (List.perm_append_comm_assoc (List.replicate b Z) L' (List.replicate b' Z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.perm_append_comm_blocks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.perm_append_comm_blocks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.perm_append_comm_blocks ``Submission.DifferentialGeometry.Topology.perm_append_comm_blocks

theorem orientedDiffeomorph_connectedSum_finiteConnectedSum_merge
    (L L' : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (b b' : ℕ) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (finiteConnectedSum (L ++ List.replicate b Z))
        (finiteConnectedSum (L' ++ List.replicate b' Z))).toClosedOrientedManifold
      (finiteConnectedSum ((L ++ L') ++ List.replicate (b + b') Z)).toClosedOrientedManifold) :=
  (finiteConnectedSum_append (L ++ List.replicate b Z) (L' ++ List.replicate b' Z)).elim
    fun e => (finiteConnectedSum_perm_orientedDiffeomorph
      (perm_append_comm_blocks L L' Z b b')).elim fun f => ⟨e.symm.trans f⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_merge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_merge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_merge ``Submission.DifferentialGeometry.Topology.orientedDiffeomorph_connectedSum_finiteConnectedSum_merge

namespace MarkedManifoldGraph

theorem oneVertexBlockStepLaw (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) : BlockStepLaw (oneVertex N) Z where
  initial := ⟨PartialRealization.oneVertexEmpty N,
    PartialRealization.componentCorrespondence_oneVertexEmpty N,
    ⟨fun _ => 0, fun _ _ _ => rfl, fun v y => by
      rw [vertexBlockList_empty, List.replicate_zero, List.append_nil,
        finiteConnectedSum_singleton]
      exact ⟨ClosedOrientedManifold.componentOrientedDiffeomorph N.toClosedOrientedManifold
        (ConnectedComponents.mk ((PartialRealization.oneVertexEmpty N).vertexPiece v y))⟩⟩,
    fun x => ⟨PUnit.unit,
      ⟨x, by rw [removedBallSet_empty]; exact Set.notMem_empty x⟩, rfl⟩⟩
  step := fun _ _ e _ _ => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexBlockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexBlockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexBlockStepLaw ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexBlockStepLaw

theorem exists_connectedSumPresentation_oneVertex_of_blockStepLaw
    (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ (P : PartialRealization (oneVertex N) Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum ((Finset.univ : Finset PUnit).toList.map (oneVertex N).vertexManifold ++
          List.replicate b Z)).toClosedOrientedManifold) :=
  exists_connectedSumPresentation_of_blockStepLaw (oneVertexBlockStepLaw N Z) PUnit.unit
    (fun _ _ => SimpleGraph.Reachable.of_subsingleton)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.exists_connectedSumPresentation_oneVertex_of_blockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.exists_connectedSumPresentation_oneVertex_of_blockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.exists_connectedSumPresentation_oneVertex_of_blockStepLaw ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.exists_connectedSumPresentation_oneVertex_of_blockStepLaw

abbrev twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    MarkedManifoldGraph.{0} where
  Vertex := Bool
  Edge := PEmpty.{1}
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun e => PEmpty.elim e
  vertexManifold := fun b => if b then N' else N
  flag := fun e => PEmpty.elim e
  flag_collar_disjoint := fun _ f => PEmpty.elim f.1.1
  attach := fun e => PEmpty.elim e
  attach_eq := fun e => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertexEmpty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.twoVertexEmpty

theorem not_reachable_twoVertexEmpty_empty (N N' : ConnectedClosedOrientedManifold.{0} 3) :
    ¬ ((twoVertexEmpty N N').processedGraph (∅ : Finset PEmpty.{1})).Reachable _root_.Bool.false true := by
  rw [show (twoVertexEmpty N N').processedGraph (∅ : Finset PEmpty.{1}) = ⊥ from
    Finset.sup_empty, SimpleGraph.reachable_bot]
  exact Bool.false_ne_true

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_reachable_twoVertexEmpty_empty

theorem not_isPartialInvariant_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3)
    (Z : ConnectedClosedOrientedManifold.{0} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{0} 3)) :
    ¬ ∃ P : PartialRealization (twoVertexEmpty N N') ∅, P.IsPartialInvariant Z Vlist := by
  rintro ⟨P, hP⟩
  refine PartialRealization.not_isPartialInvariant_of_not_reachable
    (v := _root_.Bool.false) (v' := _root_.Bool.true) P Z Vlist (not_reachable_twoVertexEmpty_empty N N') ?_ ?_ hP
  · exact Classical.choice (nonempty_puncturedCarrier (twoVertexEmpty N N') ∅ _root_.Bool.false)
  · exact Classical.choice (nonempty_puncturedCarrier (twoVertexEmpty N N') ∅ _root_.Bool.true)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertexEmpty

theorem not_partialStepLaw_twoVertexEmpty (N N' : ConnectedClosedOrientedManifold.{0} 3)
    (Z : ConnectedClosedOrientedManifold.{0} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{0} 3)) :
    ¬ PartialStepLaw (twoVertexEmpty N N') Z Vlist :=
  fun h => not_isPartialInvariant_twoVertexEmpty N N' Z Vlist h.initial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertexEmpty

theorem not_isPartialInvariant_twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold)
    (Z : ConnectedClosedOrientedManifold.{0} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{0} 3)) :
    ¬ ∃ P : PartialRealization (twoVertex N B B') ∅, P.IsPartialInvariant Z Vlist := by
  rintro ⟨P, hP⟩
  refine PartialRealization.not_isPartialInvariant_of_not_reachable
    (v := _root_.Bool.false) (v' := _root_.Bool.true) P Z Vlist ?_ ?_ ?_ hP
  · rw [processedGraph_empty_twoVertex, SimpleGraph.reachable_bot]
    exact Bool.false_ne_true
  · exact Classical.choice (nonempty_puncturedCarrier (twoVertex N B B') ∅ _root_.Bool.false)
  · exact Classical.choice (nonempty_puncturedCarrier (twoVertex N B B') ∅ _root_.Bool.true)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_isPartialInvariant_twoVertex

theorem not_partialStepLaw_twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold)
    (Z : ConnectedClosedOrientedManifold.{0} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{0} 3)) :
    ¬ PartialStepLaw (twoVertex N B B') Z Vlist :=
  fun h => not_isPartialInvariant_twoVertex N B B' Z Vlist h.initial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertex ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_partialStepLaw_twoVertex

end MarkedManifoldGraph

end DifferentialGeometry.Topology
