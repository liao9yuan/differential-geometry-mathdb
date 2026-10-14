import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank

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

theorem componentConnectedSumDecomposition_of_cutIndices_eq_empty
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) (hL : E.CompleteEnumeration C L) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = (E.cutIndices C).card + 1 - L.length ∧
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  obtain ⟨ρ⟩ := hr C N hC hN
  obtain ⟨N', hL'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  have hNN' : N' = N := by
    have hmem : N' ∈ L := by rw [hL']; exact List.mem_singleton.mpr rfl
    have h := hL.2.1 N' hmem
    rw [hN, Set.mem_singleton_iff] at h
    exact h
  refine ⟨[], by rw [hL']; simp [hC], by simp, ?_⟩
  rw [hL', hNN']
  exact ⟨ρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutIndices_eq_empty

def cutComponentRealization : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization

def cutComponentSingleEnumeration : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L ∧
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration

theorem cutComponentRealization_iff_singleEnumeration :
    E.cutComponentRealization ↔ E.cutComponentSingleEnumeration := by
  constructor
  · intro h C hC
    obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
    obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C hC L hL
    exact ⟨L, K, hL, hKlen, hKfac, hdiff⟩
  · intro h C hC L hL
    obtain ⟨L₀, K, hL₀, hKlen, hKfac, hρ⟩ := h C hC
    have hp := E.completeEnumeration_perm hL hL₀
    refine ⟨K, ?_, hKfac, ?_⟩
    · rw [hp.length_eq]
      exact hKlen
    · obtain ⟨σ⟩ := finiteConnectedSum_perm (hp.symm.append_right K)
      exact hρ.map fun ρ => ρ.trans σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_iff_singleEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_iff_singleEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_iff_singleEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_iff_singleEnumeration

theorem cutComponentRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentRealization :=
  fun C _ L hL => h C L hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_componentConnectedSumDecomposition

theorem cutComponentSingleEnumeration_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentSingleEnumeration :=
  E.cutComponentRealization_iff_singleEnumeration.mp
    (E.cutComponentRealization_of_componentConnectedSumDecomposition h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleEnumeration_of_componentConnectedSumDecomposition

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization :
    E.componentConnectedSumDecomposition ↔ E.NoTubeRealization ∧ E.cutComponentRealization := by
  constructor
  · intro h
    exact ⟨E.noTubeRealization_of_componentConnectedSumDecomposition h,
      E.cutComponentRealization_of_componentConnectedSumDecomposition h⟩
  · rintro ⟨hr, hcut⟩ C L hL
    by_cases hC : E.cutIndices C = ∅
    · exact E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC L hL
    · exact hcut C hC L hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization

theorem noTubeRealization_of_forall_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) : E.NoTubeRealization :=
  fun C _ hC _ => absurd hC (h C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_forall_cutIndices_ne_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_forall_cutIndices_ne_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_forall_cutIndices_ne_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_forall_cutIndices_ne_empty

theorem cutComponentRealization_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : E.cutComponentRealization :=
  fun C hne => absurd (h C) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_forall_cutIndices_eq_empty

theorem componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) :
    E.componentConnectedSumDecomposition ↔ E.cutComponentRealization := by
  constructor
  · exact E.cutComponentRealization_of_componentConnectedSumDecomposition
  · intro hcut
    exact E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
      ⟨E.noTubeRealization_of_forall_cutIndices_ne_empty h, hcut⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      (∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization) ∧
        (∀ i : Fin T.eventCount, (T.transition i).cutComponentRealization) :=
  (forall_congr' fun i =>
    (T.transition i).componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization).trans
    forall_and

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization

end FiniteCutCapTrace

end DifferentialGeometry.Topology
