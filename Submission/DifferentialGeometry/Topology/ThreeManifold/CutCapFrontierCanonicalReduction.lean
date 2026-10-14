import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation

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

private theorem forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor
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
      (forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor hS
        fun F hF => h F (by simp [hF]))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor target :: scope.openDecls } }

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutComponentCanonicalGluing : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing

def cutCapSummandCanonicalCount : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (K : List (ConnectedClosedOrientedManifold.{u} 3)),
    (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) →
    K.length = E.incidenceCycleRank C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount

def sphericalSummandExponentUnique (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (b b' : ℕ),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b' S)).toClosedOrientedManifold) →
    b = b'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique

def cutCapCanonicalFrontiers : Prop :=
  E.cutComponentCanonicalGluing ∧ E.cutCapSummandCanonicalCount

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers

theorem cutComponentGluing_iff_cutComponentCanonicalGluing :
    E.cutComponentGluing ↔ E.cutComponentCanonicalGluing := by
  constructor
  · intro h C hC
    exact h C hC (E.canonicalEnumeration C) (E.completeEnumeration_canonicalEnumeration C)
  · intro h C hC L hL
    obtain ⟨K, hKfac, hdiff⟩ := h C hC
    have hp := (E.completeEnumeration_perm hL
      (E.completeEnumeration_canonicalEnumeration C)).append_right K
    obtain ⟨σ⟩ := finiteConnectedSum_perm hp
    exact ⟨K, hKfac, hdiff.map fun ρ => ρ.trans σ.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCanonicalGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCanonicalGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCanonicalGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCanonicalGluing

theorem cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentCanonicalGluing :=
  fun C hC => absurd (h C) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty

theorem cutComponentCanonicalGluing_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentCanonicalGluing :=
  E.cutComponentGluing_iff_cutComponentCanonicalGluing.mp
    (E.cutComponentGluing_of_cutComponentRealization
      (E.cutComponentRealization_of_componentConnectedSumDecomposition h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_componentConnectedSumDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_componentConnectedSumDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_componentConnectedSumDecomposition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_componentConnectedSumDecomposition

theorem cutComponentCanonicalGluing_of_sphericalGraphSumRealization
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.cutComponentCanonicalGluing := by
  intro C _
  refine ⟨List.replicate (E.incidenceCycleRank C) S, fun F hF => ?_, h C⟩
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
  exact hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_of_sphericalGraphSumRealization

theorem cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount :
    E.cutCapSummandCountDetermined ↔ E.cutCapSummandCanonicalCount := by
  constructor
  · intro h C K hKfac hdiff
    rw [incidenceCycleRank, ← E.length_canonicalEnumeration C]
    exact h C (E.canonicalEnumeration C) K
      (E.completeEnumeration_canonicalEnumeration C) hKfac hdiff
  · intro h C L K hL hKfac hdiff
    have hp := (E.completeEnumeration_perm hL
      (E.completeEnumeration_canonicalEnumeration C)).append_right K
    obtain ⟨σ⟩ := finiteConnectedSum_perm hp
    rw [h C K hKfac (hdiff.map fun ρ => ρ.trans σ), incidenceCycleRank,
      E.ncard_associatedFactors_eq_length hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount

theorem noTubeRealization_iff_canonicalEnumeration :
    E.NoTubeRealization ↔
      ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅ →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  constructor
  · intro hr C hC
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    obtain ⟨N', hN'⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
    have hmem : N ∈ E.associatedFactors C :=
      (E.completeEnumeration_canonicalEnumeration C).2.1 N (hN ▸ List.mem_singleton.mpr rfl)
    rw [hN'] at hmem
    have hNN : N = N' := Set.mem_singleton_iff.mp hmem
    have hres := hr C N' hC hN'
    rw [← hNN] at hres
    simpa [hN] using hres
  · intro h C N hC hN
    obtain ⟨N', hN'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    have hmem : N' ∈ E.associatedFactors C :=
      (E.completeEnumeration_canonicalEnumeration C).2.1 N' (hN' ▸ List.mem_singleton.mpr rfl)
    rw [hN] at hmem
    have hN'N : N' = N := Set.mem_singleton_iff.mp hmem
    have hres := h C hC
    rw [hN', hN'N] at hres
    simpa using hres

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_canonicalEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_canonicalEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_canonicalEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_canonicalEnumeration

theorem cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hglue : E.cutComponentCanonicalGluing) (hcount : E.cutCapSummandCanonicalCount) :
    E.cutComponentRealization :=
  E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr hglue)
    (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr hcount)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount

theorem cutComponentRealization_of_cutCapCanonicalFrontiers
    (h : E.cutCapCanonicalFrontiers) : E.cutComponentRealization :=
  E.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount h.1 h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutCapCanonicalFrontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutCapCanonicalFrontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutCapCanonicalFrontiers ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentRealization_of_cutCapCanonicalFrontiers

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
    (hr : E.NoTubeRealization) (h : E.cutCapCanonicalFrontiers) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨hr, E.cutComponentRealization_of_cutCapCanonicalFrontiers h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers

theorem sphericalSummandExponentUnique_of_cutCapSummandCountDetermined
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.cutCapSummandCountDetermined) : E.sphericalSummandExponentUnique S := by
  intro C b b' hb hb'
  have hfac : ∀ b : ℕ, ∀ F ∈ List.replicate b S, isSphereTwoTimesCircleFactor F := by
    intro b F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  have h1 := h C (E.canonicalEnumeration C) (List.replicate b S)
    (E.completeEnumeration_canonicalEnumeration C) (hfac b) hb
  have h2 := h C (E.canonicalEnumeration C) (List.replicate b' S)
    (E.completeEnumeration_canonicalEnumeration C) (hfac b') hb'
  rw [List.length_replicate] at h1 h2
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_cutCapSummandCountDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_cutCapSummandCountDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_cutCapSummandCountDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentUnique_of_cutCapSummandCountDetermined

theorem cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S) (huniq : E.sphericalSummandExponentUnique S) :
    E.cutCapSummandCountDetermined := by
  refine E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr ?_
  intro C K hKfac hdiff
  obtain ⟨σ⟩ := finiteConnectedSum_congr_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds)
    (List.rel_append (List.forall₂_same.mpr fun A _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
      (forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor hS hKfac))
  exact huniq C K.length (E.incidenceCycleRank C) (hdiff.map fun ρ => ρ.trans σ) (hex C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique

theorem cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S) (huniq : E.sphericalSummandExponentUnique S) :
    E.cutCapCanonicalFrontiers :=
  ⟨E.cutComponentCanonicalGluing_of_sphericalGraphSumRealization hS hex,
    E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mp
      (E.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
        hS hex huniq)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hr : E.NoTubeRealization) (hglue : E.cutComponentCanonicalGluing)
    (hcount : E.cutCapSummandCanonicalCount) : E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    hr (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr hglue)
    (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr hcount)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount

theorem exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) :
    E.cutIndices C = ∅ ∧ (E.cutIncidenceGraph C).Connected :=
  ⟨E.cutIndices_eq_empty_of_isEmpty_index C, E.cutIncidenceGraph_connected C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected

theorem not_forall_cutIndices_ne_empty_of_isEmpty_index [IsEmpty E.tubes.Index] :
    ¬ ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ :=
  fun h => h (ConnectedComponents.mk (Classical.choice E.source_nonempty))
    (E.cutIndices_eq_empty_of_isEmpty_index _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_forall_cutIndices_ne_empty_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_forall_cutIndices_ne_empty_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_forall_cutIndices_ne_empty_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_forall_cutIndices_ne_empty_of_isEmpty_index

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem cutComponentRealization_of_cutCapCanonicalFrontiers
    (h : ∀ i : Fin T.eventCount, (T.transition i).cutCapCanonicalFrontiers) :
    ∀ i : Fin T.eventCount, (T.transition i).cutComponentRealization :=
  fun i => by
    let E := T.transition i
    exact E.cutComponentRealization_of_cutCapCanonicalFrontiers (h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.cutComponentRealization_of_cutCapCanonicalFrontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.cutComponentRealization_of_cutCapCanonicalFrontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.cutComponentRealization_of_cutCapCanonicalFrontiers ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.cutComponentRealization_of_cutCapCanonicalFrontiers

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (h : ∀ i : Fin T.eventCount, (T.transition i).cutCapCanonicalFrontiers) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => by
    let E := T.transition i
    exact E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
      (hr i) (h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentCanonicalGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCanonicalCount) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  T.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    hr
    (fun i => (T.transition i).cutComponentGluing_iff_cutComponentCanonicalGluing.mpr (hglue i))
    (fun i =>
      (T.transition i).cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr (hcount i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount

end FiniteCutCapTrace

end DifferentialGeometry.Topology
