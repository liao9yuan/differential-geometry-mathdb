import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapFactorNormalization
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapNoTubeReduction

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

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

noncomputable def canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    List (ConnectedClosedOrientedManifold.{u} 3) :=
  Classical.choose (E.exists_completeEnumeration C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.canonicalEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.canonicalEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.canonicalEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.canonicalEnumeration

theorem completeEnumeration_canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    E.CompleteEnumeration C (E.canonicalEnumeration C) :=
  Classical.choose_spec (E.exists_completeEnumeration C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.completeEnumeration_canonicalEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.completeEnumeration_canonicalEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.completeEnumeration_canonicalEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.completeEnumeration_canonicalEnumeration

theorem length_canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    (E.canonicalEnumeration C).length = (E.associatedFactors C).ncard :=
  (E.ncard_associatedFactors_eq_length (E.completeEnumeration_canonicalEnumeration C)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.length_canonicalEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.length_canonicalEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.length_canonicalEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.length_canonicalEnumeration

def graphSumRealization : Prop :=
  ∀ C : ConnectedComponents M.Carrier,
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization

def sphericalGraphSumRealization (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents M.Carrier,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization

def cutGraphSumRealization : Prop :=
  ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization

theorem graphSumRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.graphSumRealization :=
  fun C => E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h
    (E.completeEnumeration_canonicalEnumeration C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_componentConnectedSumDecomposition

theorem componentConnectedSumDecomposition_of_graphSumRealization
    (h : E.graphSumRealization) : E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun {L L'} hp => finiteConnectedSum_perm hp) ?_
  intro C
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨E.canonicalEnumeration C, E.completeEnumeration_canonicalEnumeration C, K,
    by
      have hb := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [E.length_canonicalEnumeration C]
      omega,
    hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_graphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_graphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_graphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_graphSumRealization

theorem graphSumRealization_iff_componentConnectedSumDecomposition :
    E.graphSumRealization ↔ E.componentConnectedSumDecomposition :=
  ⟨E.componentConnectedSumDecomposition_of_graphSumRealization,
    E.graphSumRealization_of_componentConnectedSumDecomposition⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_componentConnectedSumDecomposition

theorem graphSumRealization_iff_localReconstruction :
    E.graphSumRealization ↔ E.localReconstruction :=
  E.graphSumRealization_iff_componentConnectedSumDecomposition.trans
    E.localReconstruction_iff_componentConnectedSumDecomposition.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_localReconstruction ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_localReconstruction

theorem graphSumRealization_iff_noTubeRealization_and_cutComponentRealization :
    E.graphSumRealization ↔ E.NoTubeRealization ∧ E.cutComponentRealization :=
  E.graphSumRealization_iff_componentConnectedSumDecomposition.trans
    E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization

theorem graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization :
    E.graphSumRealization ↔ E.NoTubeRealization ∧ E.cutGraphSumRealization := by
  constructor
  · intro h
    exact ⟨E.noTubeRealization_of_componentConnectedSumDecomposition
        (E.componentConnectedSumDecomposition_of_graphSumRealization h),
      fun C _ => h C⟩
  · rintro ⟨hr, hcut⟩ C
    by_cases hC : E.cutIndices C = ∅
    · obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
        E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC
          (E.canonicalEnumeration C) (E.completeEnumeration_canonicalEnumeration C)
      refine ⟨K, ?_, hKfac, hdiff⟩
      have hle := E.ncard_associatedFactors_le_card_cutIndices_add_one C
      have hsum := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [hKlen, E.length_canonicalEnumeration C]
      omega
    · exact hcut C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization

theorem sphericalGraphSumRealization_of_componentConnectedSumDecomposition
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.componentConnectedSumDecomposition) : E.sphericalGraphSumRealization S := by
  intro C
  have hb : E.incidenceCycleRank C + (E.canonicalEnumeration C).length =
      (E.cutIndices C).card + 1 := by
    rw [E.length_canonicalEnumeration C, E.incidenceCycleRank_add_ncard_associatedFactors C]
  exact (E.componentConnectedSumDecomposition_iff_fixedSphericalModel S hS).mp h C
    (E.canonicalEnumeration C) (E.incidenceCycleRank C)
    (E.completeEnumeration_canonicalEnumeration C) hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_componentConnectedSumDecomposition

theorem componentConnectedSumDecomposition_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun {L L'} hp => finiteConnectedSum_perm hp) ?_
  intro C
  exact ⟨E.canonicalEnumeration C, E.completeEnumeration_canonicalEnumeration C,
    List.replicate (E.incidenceCycleRank C) S,
    by
      have hb := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [List.length_replicate, E.length_canonicalEnumeration C]
      omega,
    fun F hF => by
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
      exact hS,
    h C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_sphericalGraphSumRealization

theorem sphericalGraphSumRealization_iff_componentConnectedSumDecomposition
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.sphericalGraphSumRealization S ↔ E.componentConnectedSumDecomposition :=
  ⟨E.componentConnectedSumDecomposition_of_sphericalGraphSumRealization S hS,
    E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition

theorem sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor
    (S S' : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) (hS' : isSphereTwoTimesCircleFactor S') :
    E.sphericalGraphSumRealization S ↔ E.sphericalGraphSumRealization S' :=
  (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).trans
    (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S' hS').symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor

theorem graphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) : E.graphSumRealization :=
  E.graphSumRealization_of_componentConnectedSumDecomposition
    (E.componentConnectedSumDecomposition_of_isEmpty_index hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_isEmpty_index

theorem sphericalGraphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) : E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_isEmpty_index hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_isEmpty_index

theorem exists_ne_nil_of_incidenceCycleRank_pos (h : E.graphSumRealization)
    (C : ConnectedComponents M.Carrier) (hpos : 0 < E.incidenceCycleRank C) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K ≠ [] ∧ K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨K, fun hnil => by rw [hnil, List.length_nil] at hKlen; omega, hKlen, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_ne_nil_of_incidenceCycleRank_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_ne_nil_of_incidenceCycleRank_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_ne_nil_of_incidenceCycleRank_pos ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_ne_nil_of_incidenceCycleRank_pos

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_graphSumRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).graphSumRealization :=
  forall_congr' fun i =>
    ((T.transition i).graphSumRealization_iff_componentConnectedSumDecomposition).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_graphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_graphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_graphSumRealization ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_graphSumRealization

theorem componentConnectedSumDecomposition_iff_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).sphericalGraphSumRealization S :=
  forall_congr' fun i =>
    ((T.transition i).sphericalGraphSumRealization_iff_componentConnectedSumDecomposition
      S hS).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_sphericalGraphSumRealization

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      (∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization) ∧
        (∀ i : Fin T.eventCount, (T.transition i).cutGraphSumRealization) :=
  (T.componentConnectedSumDecomposition_iff_graphSumRealization).trans
    ((forall_congr' fun i =>
      (T.transition i).graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization).trans
      forall_and)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization

end FiniteCutCapTrace

end DifferentialGeometry.Topology
