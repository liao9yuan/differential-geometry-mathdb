import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapStandardReconstruction

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

theorem finiteConnectedSum_perm {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hp : L.Perm L') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum L').toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_perm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_perm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_perm ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_perm

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def incidenceCycleRank (C : ConnectedComponents M.Carrier) : ℕ :=
  (E.cutIndices C).card + 1 - (E.associatedFactors C).ncard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank

theorem ncard_associatedFactors_le_card_cutIndices_add_one
    (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).ncard ≤ (E.cutIndices C).card + 1 := by
  classical
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨b, hb⟩ :=
    E.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected
      (E.cutIncidenceGraph_connected C) hL
  rw [E.ncard_associatedFactors_eq_length hL]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_le_card_cutIndices_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_le_card_cutIndices_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_le_card_cutIndices_add_one ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_le_card_cutIndices_add_one

theorem incidenceCycleRank_add_ncard_associatedFactors
    (C : ConnectedComponents M.Carrier) :
    E.incidenceCycleRank C + (E.associatedFactors C).ncard =
      (E.cutIndices C).card + 1 := by
  rw [incidenceCycleRank]
  exact Nat.sub_add_cancel (E.ncard_associatedFactors_le_card_cutIndices_add_one C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_ncard_associatedFactors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_ncard_associatedFactors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_ncard_associatedFactors ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_ncard_associatedFactors

theorem incidenceCycleRank_eq_zero_iff (C : ConnectedComponents M.Carrier) :
    E.incidenceCycleRank C = 0 ↔
      (E.associatedFactors C).ncard = (E.cutIndices C).card + 1 := by
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  constructor <;> intro h' <;> omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_iff ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_iff

theorem eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq
    (C : ConnectedComponents M.Carrier) {b : ℕ}
    (hb : b + (E.associatedFactors C).ncard = (E.cutIndices C).card + 1) :
    b = E.incidenceCycleRank C := by
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq

theorem edgeSet_subset_range_cutEnds (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).edgeSet ⊆ Set.range (E.cutEnds C) := by
  rintro e he
  induction e using Sym2.ind with
  | _ A B =>
    rw [SimpleGraph.mem_edgeSet, cutIncidenceGraph, SimpleGraph.fromRel_adj] at he
    rcases he with ⟨-, ⟨a, ha⟩ | ⟨a, ha⟩⟩
    · exact ⟨a, ha⟩
    · exact ⟨a, ha.trans Sym2.eq_swap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.edgeSet_subset_range_cutEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.edgeSet_subset_range_cutEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.edgeSet_subset_range_cutEnds ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.edgeSet_subset_range_cutEnds

theorem ncard_edgeSet_le_card_cutIndices (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).edgeSet.ncard ≤ (E.cutIndices C).card := by
  refine (Set.ncard_le_ncard (E.edgeSet_subset_range_cutEnds C)).trans ?_
  have h := Nat.card_le_card_of_surjective
    (fun i : ↥(E.cutIndices C) => (⟨E.cutEnds C i, i, rfl⟩ : Set.range (E.cutEnds C)))
    (by rintro ⟨y, i, rfl⟩; exact ⟨i, rfl⟩)
  rw [Nat.card_coe_set_eq] at h
  simpa [Nat.card_eq_fintype_card, Fintype.card_coe] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_edgeSet_le_card_cutIndices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_edgeSet_le_card_cutIndices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_edgeSet_le_card_cutIndices ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_edgeSet_le_card_cutIndices

theorem card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank
    (C : ConnectedComponents M.Carrier) :
    (E.cutIndices C).card - (E.cutIncidenceGraph C).edgeSet.ncard ≤
      E.incidenceCycleRank C := by
  have hE := E.ncard_edgeSet_le_card_cutIndices C
  have hV : (E.associatedFactors C).ncard ≤
      (E.cutIncidenceGraph C).edgeSet.ncard + 1 := by
    simpa using (E.cutIncidenceGraph_connected C).card_vert_le_card_edgeSet_add_one
  have hcyc := E.incidenceCycleRank_add_ncard_associatedFactors C
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank

theorem localReconstruction_iff_componentConnectedSumDecomposition :
    E.localReconstruction ↔ E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected
    fun C => E.cutIncidenceGraph_connected C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_iff_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_iff_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_iff_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_iff_componentConnectedSumDecomposition

theorem length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C L hL
  refine ⟨K, ?_, hKfac, hdiff⟩
  rw [hKlen, incidenceCycleRank, ← E.ncard_associatedFactors_eq_length hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition

theorem exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hlen : L.length = (E.cutIndices C).card + 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, -, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hKlen0 : K.length = 0 := by
    rw [hKlen, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL, hlen]
    simp
  have hK : K = [] := List.length_eq_zero_iff.mp hKlen0
  subst hK
  simpa using hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one

theorem exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hlen : L.length = (E.cutIndices C).card) :
    ∃ F : ConnectedClosedOrientedManifold.{u} 3,
      isSphereTwoTimesCircleFactor F ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ [F])).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hK1 : K.length = 1 := by
    rw [hKlen, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL, hlen]
    omega
  obtain ⟨F, hF⟩ := List.length_eq_one_iff.mp hK1
  refine ⟨F, hKfac F ?_, ?_⟩
  · rw [hF]
    exact List.mem_singleton.mpr rfl
  · rw [hF] at hdiff
    exact hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices

theorem noTubeRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.NoTubeRealization := by
  intro C N hC hN
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, hKlen, -, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hKlen0 : K.length = 0 := by
    rw [hKlen, incidenceCycleRank, hC, hN, Set.ncard_singleton]
    simp
  have hK : K = [] := List.length_eq_zero_iff.mp hKlen0
  subst hK
  rw [List.append_nil] at hdiff
  obtain ⟨N', hL'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  have hNN : N' = N := by
    have hmem : N' ∈ L := by rw [hL']; exact List.mem_singleton.mpr rfl
    have hmem' := hL.2.1 N' hmem
    rw [hN, Set.mem_singleton_iff] at hmem'
    exact hmem'
  rw [hL', hNN] at hdiff
  simpa using hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_componentConnectedSumDecomposition

theorem cutIndices_eq_empty_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) : E.cutIndices C = ∅ :=
  Finset.not_nonempty_iff_eq_empty.mp fun h => h.elim fun a _ => isEmptyElim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_of_isEmpty_index

theorem incidenceCycleRank_eq_zero_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) : E.incidenceCycleRank C = 0 := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C
    (E.cutIndices_eq_empty_of_isEmpty_index C)
  rw [incidenceCycleRank, E.cutIndices_eq_empty_of_isEmpty_index C, hN, Set.ncard_singleton]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_isEmpty_index

theorem componentConnectedSumDecomposition_of_exists_singleEnumeration
    (h : ∀ C : ConnectedComponents M.Carrier,
      ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
        E.CompleteEnumeration C L ∧
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun hp => finiteConnectedSum_perm hp) ?_
  intro C
  obtain ⟨L, K, hL, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨L, hL, K, hKlen, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_exists_singleEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_exists_singleEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_exists_singleEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_exists_singleEnumeration

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem localReconstruction_of_componentConnectedSumDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) :
    ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).mpr (h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_componentConnectedSumDecomposition

theorem componentConnectedSumDecomposition_of_exists_singleEnumeration
    (h : ∀ (i : Fin T.eventCount) (C : ConnectedComponents (T.stage i.castSucc).Carrier),
      ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
        (T.transition i).CompleteEnumeration C L ∧
        K.length = ((T.transition i).cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          ((T.stage i.castSucc).component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).componentConnectedSumDecomposition_of_exists_singleEnumeration
    (fun C => h i C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_exists_singleEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_exists_singleEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_exists_singleEnumeration ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_exists_singleEnumeration

end FiniteCutCapTrace

end DifferentialGeometry.Topology
