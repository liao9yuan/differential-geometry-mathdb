import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_append_standardThreeSphereLift
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ [standardThreeSphereLift.{u}])).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold) := by
  obtain ⟨e⟩ := finiteConnectedSum_append L [standardThreeSphereLift.{u}]
  obtain ⟨u⟩ := connectedSum_sphere_right (finiteConnectedSum L)
  exact ⟨e.trans u⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_append_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_append_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_append_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_append_standardThreeSphereLift

theorem finiteConnectedSum_additiveInvariant
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    (hunit : ι standardThreeSphereLift.{u} = 0)
    (hadd : ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
      ι (connectedSum A B) = ι A + ι B)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    ι (finiteConnectedSum L) = (L.map ι).sum := by
  induction L with
  | nil => simpa using hunit
  | cons M L ih =>
    match L, ih with
    | [], _ => simp
    | N :: L', ih =>
      rw [finiteConnectedSum_cons_cons, hadd, ih]
      simp [List.map_cons, List.sum_cons]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_additiveInvariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_additiveInvariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_additiveInvariant ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_additiveInvariant

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutComponentRealization_of_sphericalGraphSumRealization
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.cutComponentRealization := by
  intro C _ L hL
  refine ⟨List.replicate (E.incidenceCycleRank C) S, ?_, ?_, ?_⟩
  · rw [List.length_replicate]
    have hlen := E.incidenceCycleRank_add_length_of_completeEnumeration hL
    omega
  · intro F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  · obtain ⟨σ⟩ := finiteConnectedSum_perm
      ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right
        (List.replicate (E.incidenceCycleRank C) S))
    exact (h C).map fun ρ => ρ.trans σ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_sphericalGraphSumRealization

theorem sphericalSummandExponentUnique_of_additiveInvariant
    {S : ConnectedClosedOrientedManifold.{u} 3}
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    (hinv : ∀ {A B : ConnectedClosedOrientedManifold.{u} 3},
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
        B.toClosedOrientedManifold) → ι A = ι B)
    (hunit : ι standardThreeSphereLift.{u} = 0)
    (hadd : ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
      ι (connectedSum A B) = ι A + ι B)
    (hpos : 0 < ι S) : E.sphericalSummandExponentUnique S := by
  intro C b b' hb hb'
  have hbI : ι (M.component C) =
      ι (finiteConnectedSum (E.canonicalEnumeration C ++ List.replicate b S)) := hinv hb
  have hbI' : ι (M.component C) =
      ι (finiteConnectedSum (E.canonicalEnumeration C ++ List.replicate b' S)) := hinv hb'
  rw [finiteConnectedSum_additiveInvariant ι hunit hadd
      (E.canonicalEnumeration C ++ List.replicate b S)] at hbI
  rw [finiteConnectedSum_additiveInvariant ι hunit hadd
      (E.canonicalEnumeration C ++ List.replicate b' S)] at hbI'
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul] at hbI hbI'
  have hmul : b * ι S = b' * ι S := Nat.add_left_cancel (hbI.symm.trans hbI')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_additiveInvariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_additiveInvariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_additiveInvariant ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_additiveInvariant

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} := by
  intro huniq
  obtain ⟨σ⟩ := finiteConnectedSum_append_standardThreeSphereLift (E.canonicalEnumeration C)
  have hb0 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate 0 standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
    simpa using h
  have hb1 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate 1 standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
    simpa using h.map fun ρ => ρ.trans σ.symm
  exact Nat.zero_ne_one (huniq C 0 1 hb0 hb1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} :=
  E.not_sphericalSummandExponentUnique_standardThreeSphereLift C
    (E.noTubeRealization_iff_canonicalEnumeration.mp hr C hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index
    [IsEmpty E.tubes.Index] (hr : E.NoTubeRealization) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} :=
  E.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization hr
    (ConnectedComponents.mk (Classical.choice E.source_nonempty))
    (E.cutIndices_eq_empty_of_isEmpty_index _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index

end SphericalCutCapTransition

end DifferentialGeometry.Topology
