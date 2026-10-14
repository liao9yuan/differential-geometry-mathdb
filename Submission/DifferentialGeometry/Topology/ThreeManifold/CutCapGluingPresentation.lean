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

def cutComponentGluing : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing

def cutCapSummandCountDetermined : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
    (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
    K.length = (E.cutIndices C).card + 1 - L.length

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined

theorem cutComponentGluing_of_cutComponentRealization (h : E.cutComponentRealization) :
    E.cutComponentGluing := by
  intro C hC L hL
  obtain ⟨K, -, hKfac, hdiff⟩ := h C hC L hL
  exact ⟨K, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentRealization

theorem cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.cutComponentRealization := by
  intro C hC L hL
  obtain ⟨K, hKfac, hdiff⟩ := hglue C hC L hL
  exact ⟨K, hcount C L K hL hKfac hdiff, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨hr, E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hglue hcount⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined

theorem incidenceCycleRank_add_length_of_completeEnumeration
    {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L) :
    E.incidenceCycleRank C + L.length = (E.cutIndices C).card + 1 := by
  rw [← E.ncard_associatedFactors_eq_length hL]
  exact E.incidenceCycleRank_add_ncard_associatedFactors C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_length_of_completeEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_length_of_completeEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_length_of_completeEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_add_length_of_completeEnumeration

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr i) (hglue i) (hcount i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined

end FiniteCutCapTrace

end DifferentialGeometry.Topology
