import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

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

namespace SimpleGraph

theorem exists_nat_add_card_eq_card_add_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hconn : G.Connected) :
    ∃ b : ℕ, b + Fintype.card V = Fintype.card G.edgeSet + 1 := by
  have hle : Fintype.card V ≤ Fintype.card G.edgeSet + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hconn.card_vert_le_card_edgeSet_add_one
  exact ⟨Fintype.card G.edgeSet + 1 - Fintype.card V, by omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one ``Submission.DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one

theorem exists_nat_add_card_eq_card_add_one_of_ends {V I : Type*} [Fintype I]
    (ends : I → Sym2 V)
    (hconn : (SimpleGraph.fromRel fun a b : V => ∃ i, ends i = s(a, b)).Connected) :
    ∃ b : ℕ, b + Nat.card V = Fintype.card I + 1 := by
  classical
  set G := SimpleGraph.fromRel fun a b : V => ∃ i, ends i = s(a, b)
  have hsub : G.edgeSet ⊆ Set.range ends := by
    rintro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
      rcases he with ⟨-, ⟨i, hi⟩ | ⟨i, hi⟩⟩
      · exact ⟨i, hi⟩
      · exact ⟨i, hi.trans Sym2.eq_swap⟩
  have h1 : Nat.card G.edgeSet ≤ Nat.card (Set.range ends) :=
    Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
  have h2 : Nat.card (Set.range ends) ≤ Nat.card I := by
    refine Nat.card_le_card_of_surjective
      (fun i : I => (⟨ends i, ⟨i, rfl⟩⟩ : Set.range ends)) ?_
    rintro ⟨y, i, rfl⟩
    exact ⟨i, rfl⟩
  have h3 : Nat.card V ≤ Nat.card G.edgeSet + 1 := hconn.card_vert_le_card_edgeSet_add_one
  have hI : Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
  refine ⟨Fintype.card I + 1 - Nat.card V, ?_⟩
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends ``Submission.DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends

end SimpleGraph

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def sphereBasePoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphereBasePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphereBasePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphereBasePoint ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphereBasePoint

theorem mem_cutIndices_iff_exists_tube_mem_componentSet (C : ConnectedComponents M.Carrier)
    (a : E.tubes.Index) :
    a ∈ E.cutIndices C ↔
      ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
        E.tubes.tube a z ∈ ClosedOrientedManifold.componentSet M C := by
  classical
  constructor
  · intro ha
    exact ⟨(sphereBasePoint, ⟨0, by norm_num⟩), (Finset.mem_filter.mp ha).2 _⟩
  · rintro ⟨z₀, hz₀⟩
    have hz₀' : ConnectedComponents.mk (E.tubes.tube a z₀) = C := hz₀
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun z => ?_⟩
    rw [ClosedOrientedManifold.mem_componentSet]
    have hcont : Continuous fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Set.Icc (-2 : ℝ) 2 => ConnectedComponents.mk (E.tubes.tube a z) :=
      ConnectedComponents.continuous_coe.comp (E.tubes.tube a).continuous
    have hpre : IsPreconnected (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Set.Icc (-2 : ℝ) 2)) := by
      have hicc : PreconnectedSpace ↥(Set.Icc (-2 : ℝ) 2) :=
        isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Icc (a := (-2 : ℝ)) (b := 2))
      simpa only [Set.univ_prod_univ] using isPreconnected_univ.prod _root_.PreconnectedSpace.isPreconnected_univ
    have hconst : ConnectedComponents.mk (E.tubes.tube a z₀) =
        ConnectedComponents.mk (E.tubes.tube a z) :=
      (hpre.image _ hcont.continuousOn).subsingleton ⟨z₀, trivial, rfl⟩ ⟨z, trivial, rfl⟩
    rw [← hconst]
    exact hz₀'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_iff_exists_tube_mem_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_iff_exists_tube_mem_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_iff_exists_tube_mem_componentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_iff_exists_tube_mem_componentSet

theorem mk_coreBoundarySphere_eq (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ConnectedComponents.mk (E.tubes.coreBoundarySphere (a.1, side) z).1 = C := by
  classical
  have ha := (Finset.mem_filter.mp a.2).2
  have hz : E.tubes.boundarySphere (a.1, side) z ∈
      ClosedOrientedManifold.componentSet M C :=
    ha (z, SphericalTubeSystem.boundaryLevel side)
  have hval : (E.tubes.coreBoundarySphere (a.1, side) z).1 =
      E.tubes.boundarySphere (a.1, side) z := rfl
  rw [hval]
  exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mk_coreBoundarySphere_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mk_coreBoundarySphere_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mk_coreBoundarySphere_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mk_coreBoundarySphere_eq

def cutCoreComponent (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cappedCutComponents C :=
  ⟨ConnectedComponents.mk (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a.1, side) z)),
    E.tubes.coreBoundarySphere (a.1, side) z,
    E.mk_coreBoundarySphere_eq C a side z, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent

theorem cutCoreComponent_eq (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cutCoreComponent C a side z = E.cutCoreComponent C a side z' := by
  refine Subtype.ext ?_
  have hcont : Continuous fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ConnectedComponents.mk (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a.1, side) z)) :=
    ConnectedComponents.continuous_coe.comp
      (E.capping.coreInclusion.continuous.comp
        (E.tubes.coreBoundarySphere (a.1, side)).continuous)
  exact (isPreconnected_univ.image _ hcont.continuousOn).subsingleton
    ⟨z, trivial, rfl⟩ ⟨z', trivial, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCoreComponent_eq

def cutEndFactor (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ↥(E.associatedFactors C) :=
  ⟨E.cappedFactor C (E.cutCoreComponent C a side z), by
    rw [E.associatedFactors_eq_range_cappedFactor]
    exact ⟨E.cutCoreComponent C a side z, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor

theorem cutEndFactor_eq (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cutEndFactor C a side z = E.cutEndFactor C a side z' := by
  exact Subtype.ext (congrArg (E.cappedFactor C) (E.cutCoreComponent_eq C a side z z'))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_eq

def cutEnds (C : ConnectedComponents M.Carrier) (a : E.cutIndices C) :
    Sym2 ↥(E.associatedFactors C) :=
  s(E.cutEndFactor C a _root_.Bool.false sphereBasePoint, E.cutEndFactor C a _root_.Bool.true sphereBasePoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEnds ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutEnds

def cutIncidenceGraph (C : ConnectedComponents M.Carrier) :
    SimpleGraph ↥(E.associatedFactors C) :=
  SimpleGraph.fromRel fun A B : ↥(E.associatedFactors C) =>
    ∃ a : E.cutIndices C, E.cutEnds C a = s(A, B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph

theorem cutIncidenceGraph_adj (C : ConnectedComponents M.Carrier)
    (A B : ↥(E.associatedFactors C)) :
    (E.cutIncidenceGraph C).Adj A B ↔
      A ≠ B ∧ (∃ a : E.cutIndices C, E.cutEnds C a = s(A, B)) := by
  rw [cutIncidenceGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, ⟨h.choose, h.choose_spec.trans Sym2.eq_swap⟩⟩
  · exact fun h => ⟨h.1, Or.inl h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_adj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_adj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_adj ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_adj

theorem ncard_associatedFactors_eq_length {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) :
    (E.associatedFactors C).ncard = L.length := by
  classical
  have hset : E.associatedFactors C = (L.toFinset : Set _) := by
    ext N
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact ⟨fun h => hL.2.2 N h, fun h => hL.2.1 N h⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_length ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_length

theorem exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected
    {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hconn : (E.cutIncidenceGraph C).Connected) (hL : E.CompleteEnumeration C L) :
    ∃ b : ℕ, b + L.length = (E.cutIndices C).card + 1 := by
  obtain ⟨b, hb⟩ := SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends
    (E.cutEnds C) (by simpa [cutIncidenceGraph] using hconn)
  rw [Nat.card_coe_set_eq, E.ncard_associatedFactors_eq_length hL, Fintype.card_coe] at hb
  exact ⟨b, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected

def componentConnectedSumDecomposition : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition

theorem localReconstruction_of_incidenceGluing
    (hconn : ∀ C : ConnectedComponents M.Carrier, (E.cutIncidenceGraph C).Connected)
    (hsum : E.componentConnectedSumDecomposition) : E.localReconstruction := by
  intro C L hL
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := hsum C L hL
  obtain ⟨b, hb⟩ :=
    E.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected (hconn C) hL
  exact ⟨K.length, K, rfl, hKfac, by omega, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_incidenceGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_incidenceGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_incidenceGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_incidenceGluing

theorem componentConnectedSumDecomposition_of_localReconstruction
    (h : E.localReconstruction) : E.componentConnectedSumDecomposition := by
  intro C L hL
  obtain ⟨b, K, hKlen, hKfac, hcount, hdiff⟩ := h C L hL
  exact ⟨K, by omega, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_localReconstruction ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_localReconstruction

theorem localReconstruction_of_componentConnectedSumDecomposition
    (hcount : ∀ (C : ConnectedComponents M.Carrier)
      (L : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L → L.length ≤ (E.cutIndices C).card + 1)
    (h : E.componentConnectedSumDecomposition) : E.localReconstruction := by
  intro C L hL
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C L hL
  exact ⟨K.length, K, rfl, hKfac, by have := hcount C L hL; omega, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_componentConnectedSumDecomposition

theorem componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected
    (hconn : ∀ C : ConnectedComponents M.Carrier, (E.cutIncidenceGraph C).Connected) :
    E.localReconstruction ↔ E.componentConnectedSumDecomposition := by
  refine ⟨E.componentConnectedSumDecomposition_of_localReconstruction, fun h => ?_⟩
  refine E.localReconstruction_of_componentConnectedSumDecomposition (fun C L hL => ?_) h
  obtain ⟨b, hb⟩ := E.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected
    (hconn C) hL
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentwise_isPoincareStandard_of_incidenceGluing
    (hconn : ∀ i : Fin T.eventCount, ∀ C : ConnectedComponents (T.stage i.castSucc).Carrier,
      ((T.transition i).cutIncidenceGraph C).Connected)
    (hsum : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsumClosed : poincareStandardSumClosed.{u}) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier :=
  T.componentwise_isPoincareStandard
    (fun i => (T.transition i).localReconstruction_of_incidenceGluing (hconn i) (hsum i))
    hctrl hext hsumClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_incidenceGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_incidenceGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_incidenceGluing ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_incidenceGluing

end FiniteCutCapTrace

end DifferentialGeometry.Topology
