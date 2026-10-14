import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumLocalization
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalExponentReduction

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

private theorem forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    ∀ {K : List (ConnectedClosedOrientedManifold.{u} 3)},
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          A.toClosedOrientedManifold B.toClosedOrientedManifold)) K
        (List.replicate K.length S)
  | [], _ => by simp
  | a :: t, h => by
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons
      (nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor (h a (by simp)) hS)
      (forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor hS
        fun F hF => h F (by simp [hF]))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor target :: scope.openDecls } }

private theorem exists_orientedDiffeomorph_finiteConnectedSum_replicate
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hKfac : ∀ F ∈ K, isSphereTwoTimesCircleFactor F) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ List.replicate K.length S)).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds)
    (List.rel_append (List.forall₂_same.mpr fun _ _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
      (forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor hS hKfac))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_orientedDiffeomorph_finiteConnectedSum_replicate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_orientedDiffeomorph_finiteConnectedSum_replicate target :: scope.openDecls } }

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutSphericalGraphSumRealization (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization

theorem cutSphericalGraphSumRealization_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.sphericalGraphSumRealization S) : E.cutSphericalGraphSumRealization S :=
  fun C _ => h C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization

theorem cutSphericalGraphSumRealization_of_cutGraphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutGraphSumFrontier S) : E.cutSphericalGraphSumRealization S :=
  fun C hC => by
    obtain ⟨b, hb⟩ := h.1 C hC
    rw [← h.2 C b hb]
    exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_cutGraphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_cutGraphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_cutGraphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_cutGraphSumFrontier

theorem sphericalSummandCompletion_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutSphericalGraphSumRealization S) : E.sphericalSummandCompletion S :=
  fun C hC => ⟨E.incidenceCycleRank C, h C hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutSphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutSphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutSphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutSphericalGraphSumRealization

theorem
    cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.cutGraphSumFrontier S ↔
      E.cutSphericalGraphSumRealization S ∧ E.sphericalSummandExponentDetermined S :=
  ⟨fun h => ⟨E.cutSphericalGraphSumRealization_of_cutGraphSumFrontier S h, h.2⟩,
    fun h => ⟨E.sphericalSummandCompletion_of_cutSphericalGraphSumRealization S h.1, h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined

theorem cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutSphericalGraphSumRealization S :=
  fun C hC => absurd (h C) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty

theorem cutSphericalGraphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (S : ConnectedClosedOrientedManifold.{u} 3) : E.cutSphericalGraphSumRealization S :=
  E.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty S
    fun C => E.cutIndices_eq_empty_of_isEmpty_index C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_of_isEmpty_index

theorem sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hr : E.NoTubeRealization)
    (h : E.cutSphericalGraphSumRealization S) : E.sphericalGraphSumRealization S := by
  intro C
  by_cases hC : E.cutIndices C = ∅
  · obtain ⟨ρ⟩ := (E.noTubeRealization_iff_canonicalEnumeration.mp hr) C hC
    rw [E.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty C hC]
    exact ⟨by simpa using ρ⟩
  · exact h C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization

theorem sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.sphericalGraphSumRealization S ↔
      E.NoTubeRealization ∧ E.cutSphericalGraphSumRealization S :=
  ⟨fun h => ⟨E.noTubeRealization_of_sphericalGraphSumRealization S h,
      E.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization S h⟩,
    fun h => E.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization
      S h.1 h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization

theorem cutSphericalGraphSumRealization_iff_cutGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.cutSphericalGraphSumRealization S ↔ E.cutGraphSumRealization := by
  constructor
  · intro h C hC
    exact ⟨List.replicate (E.incidenceCycleRank C) S, by simp,
      fun F hF => by
        obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
        exact hS,
      h C hC⟩
  · intro h C hC
    obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C hC
    obtain ⟨σ⟩ := exists_orientedDiffeomorph_finiteConnectedSum_replicate
      (L := E.canonicalEnumeration C) hS hKfac
    rw [hKlen] at σ
    exact hdiff.map fun ρ => ρ.trans σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_iff_cutGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_iff_cutGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_iff_cutGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutSphericalGraphSumRealization_iff_cutGraphSumRealization

theorem exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ∀ b : ℕ, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
  intro b
  induction b with
  | zero => simpa using h
  | succ b ih =>
    obtain ⟨ρ⟩ := ih
    obtain ⟨σ⟩ := finiteConnectedSum_append_standardThreeSphereLift
      (E.canonicalEnumeration C ++ List.replicate b standardThreeSphereLift.{u})
    rw [List.append_assoc] at σ
    rw [List.replicate_succ']
    exact ⟨ρ.trans σ.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift

theorem not_sphericalSummandExponentDetermined_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.sphericalSummandExponentDetermined standardThreeSphereLift.{u} := by
  intro hdet
  have h0 := hdet C 0 (by simpa using h)
  have h1 := hdet C 1 (by
    simpa using
      E.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift C h 1)
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentDetermined_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentDetermined_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentDetermined_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_sphericalSummandExponentDetermined_standardThreeSphereLift

theorem not_cutGraphSumFrontier_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.cutGraphSumFrontier standardThreeSphereLift.{u} :=
  fun hf => E.not_sphericalSummandExponentDetermined_standardThreeSphereLift C h hf.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_cutGraphSumFrontier_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_cutGraphSumFrontier_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_cutGraphSumFrontier_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_cutGraphSumFrontier_standardThreeSphereLift

end SphericalCutCapTransition

end DifferentialGeometry.Topology
