import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

private def tubeBasePoint :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2 :=
  (⟨EuclideanSpace.single 0 1, by simp⟩, ⟨0, by norm_num⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.tubeBasePoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.tubeBasePoint target :: scope.openDecls } }

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_cutIndices_ne_empty_of_nonempty_index (h : Nonempty E.tubes.Index) :
    ∃ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ := by
  obtain ⟨a⟩ := h
  refine ⟨ConnectedComponents.mk (E.tubes.tube a tubeBasePoint), fun hcut => ?_⟩
  have hmem : a ∈ E.cutIndices (ConnectedComponents.mk (E.tubes.tube a tubeBasePoint)) :=
    (E.mem_cutIndices_iff_exists_tube_mem_componentSet _ a).mpr
      ⟨tubeBasePoint, by
        rw [ClosedOrientedManifold.componentSet_mk]
        exact mem_connectedComponent⟩
  rw [hcut] at hmem
  exact Finset.notMem_empty a hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_ne_empty_of_nonempty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_ne_empty_of_nonempty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_ne_empty_of_nonempty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_ne_empty_of_nonempty_index

theorem isEmpty_index_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : IsEmpty E.tubes.Index :=
  ⟨fun a => (E.exists_cutIndices_ne_empty_of_nonempty_index ⟨a⟩).elim fun C hC => hC (h C)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isEmpty_index_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isEmpty_index_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isEmpty_index_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isEmpty_index_of_forall_cutIndices_eq_empty

theorem cutComponentGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : E.cutComponentGluing :=
  fun C hne => absurd (h C) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_forall_cutIndices_eq_empty

theorem exists_singleton_associatedFactors_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) :
    ∃ N : ConnectedClosedOrientedManifold.{u} 3, E.associatedFactors C = {N} :=
  E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C
    (E.cutIndices_eq_empty_of_isEmpty_index C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_singleton_associatedFactors_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_singleton_associatedFactors_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_singleton_associatedFactors_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_singleton_associatedFactors_of_isEmpty_index

theorem ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    (E.associatedFactors C).ncard = 1 ∨ (E.associatedFactors C).ncard = 2 := by
  have hle := E.ncard_associatedFactors_le_card_cutIndices_add_one C
  have hpos : 0 < (E.associatedFactors C).ncard :=
    (Set.ncard_pos (E.associatedFactors_finite C)).mpr (E.associatedFactors_nonempty C)
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one

theorem sphericalGraphSumRealization_singleTube_dichotomy
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.sphericalGraphSumRealization S)
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ [S])).toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  rcases E.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one C hcard with h1 | h2
  · left
    have hcyc : E.incidenceCycleRank C = 1 := by
      rw [incidenceCycleRank, hcard, h1]
    have hC := h C
    rw [hcyc] at hC
    simpa using hC
  · right
    have hcyc : E.incidenceCycleRank C = 0 := by
      rw [incidenceCycleRank, hcard, h2]
    have hC := h C
    rw [hcyc] at hC
    simpa using hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_singleTube_dichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_singleTube_dichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_singleTube_dichotomy ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_singleTube_dichotomy

theorem localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) : E.localReconstruction :=
  E.localReconstruction_of_incidenceGluing (fun C => E.cutIncidenceGraph_connected C)
    (E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hr hglue hcount)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined

theorem exists_summandCompletion_of_cutIndices_eq_empty (hr : E.NoTubeRealization)
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L ∧ (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) ∧
        K.length = (E.cutIndices C).card + 1 - L.length := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
    E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC L hL
  exact ⟨L, K, hL, hKfac, hdiff, hKlen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_summandCompletion_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_summandCompletion_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_summandCompletion_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_summandCompletion_of_cutIndices_eq_empty

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  fun i =>
    (T.transition i).localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      (hr i) (hglue i) (hcount i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined

end FiniteCutCapTrace

end DifferentialGeometry.Topology
