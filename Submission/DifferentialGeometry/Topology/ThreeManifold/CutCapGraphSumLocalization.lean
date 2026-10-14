import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction

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

private theorem forall_mem_replicate_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) (b : ℕ) :
    ∀ F ∈ List.replicate b S, isSphereTwoTimesCircleFactor F := by
  intro F hF
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
  exact hS

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.forall_mem_replicate_isSphereTwoTimesCircleFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.forall_mem_replicate_isSphereTwoTimesCircleFactor target :: scope.openDecls } }

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def sphericalSummandCompletion (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ → ∃ b : ℕ,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion

def sphericalSummandExponentDetermined (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (b : ℕ),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold) →
    b = E.incidenceCycleRank C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandExponentDetermined

def cutGraphSumFrontier (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  E.sphericalSummandCompletion S ∧ E.sphericalSummandExponentDetermined S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumFrontier

def graphSumFrontier (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  E.NoTubeRealization ∧ E.cutGraphSumFrontier S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier

theorem cutComponentCanonicalGluing_iff_sphericalSummandCompletion
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.cutComponentCanonicalGluing ↔ E.sphericalSummandCompletion S := by
  constructor
  · intro h C hC
    obtain ⟨K, hKfac, hdiff⟩ := h C hC
    obtain ⟨σ⟩ := exists_orientedDiffeomorph_finiteConnectedSum_replicate hS hKfac
    exact ⟨K.length, hdiff.map fun ρ => ρ.trans σ⟩
  · intro h C hC
    obtain ⟨b, hdiff⟩ := h C hC
    exact ⟨List.replicate b S, forall_mem_replicate_isSphereTwoTimesCircleFactor hS b, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_iff_sphericalSummandCompletion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_iff_sphericalSummandCompletion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_iff_sphericalSummandCompletion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCanonicalGluing_iff_sphericalSummandCompletion

theorem cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.cutCapSummandCanonicalCount ↔ E.sphericalSummandExponentDetermined S := by
  constructor
  · intro h C b hdiff
    have hlen := h C (List.replicate b S)
      (forall_mem_replicate_isSphereTwoTimesCircleFactor hS b) hdiff
    simpa using hlen
  · intro h C K hKfac hdiff
    obtain ⟨σ⟩ := exists_orientedDiffeomorph_finiteConnectedSum_replicate hS hKfac
    have hlen := h C K.length (hdiff.map fun ρ => ρ.trans σ)
    simpa using hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined

theorem sphericalSummandCompletion_of_cutGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.cutGraphSumRealization) : E.sphericalSummandCompletion S :=
  (E.cutComponentCanonicalGluing_iff_sphericalSummandCompletion S hS).mp
    fun C hC => by
      obtain ⟨K, -, hKfac, hdiff⟩ := h C hC
      exact ⟨K, hKfac, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_cutGraphSumRealization

theorem cutGraphSumRealization_of_cutGraphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.cutGraphSumFrontier S) : E.cutGraphSumRealization :=
  fun C hC => by
    obtain ⟨b, hdiff⟩ := h.1 C hC
    exact ⟨List.replicate b S, by simpa using h.2 C b hdiff,
      forall_mem_replicate_isSphereTwoTimesCircleFactor hS b, hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_cutGraphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_cutGraphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_cutGraphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_cutGraphSumFrontier

theorem noTubeRealization_iff_forall_range_tube_inter_componentSet_eq_empty :
    E.NoTubeRealization ↔
      ∀ (C : ConnectedComponents M.Carrier),
        (∀ a : E.tubes.Index, _root_.Set.range (E.tubes.tube a) ∩
          ClosedOrientedManifold.componentSet M C = ∅) →
        ∀ N : ConnectedClosedOrientedManifold.{u} 3, E.associatedFactors C = {N} →
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold) := by
  constructor
  · intro h C hdisj N hN
    refine h C N ((E.cutIndices_eq_empty_iff C).mpr fun a => ?_) hN
    rintro ⟨z, hz⟩
    have hdisj_a := hdisj a
    rw [Set.eq_empty_iff_forall_notMem] at hdisj_a
    exact hdisj_a (E.tubes.tube a z) ⟨Set.mem_range_self z, hz⟩
  · intro h C N hC hN
    refine h C (fun a => ?_) N hN
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨z, rfl⟩, hy⟩
    exact Finset.notMem_empty a (hC ▸
      (E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mpr ⟨z, hy⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_forall_range_tube_inter_componentSet_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_forall_range_tube_inter_componentSet_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_forall_range_tube_inter_componentSet_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_iff_forall_range_tube_inter_componentSet_eq_empty

theorem graphSumRealization_iff_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.graphSumRealization ↔ E.sphericalGraphSumRealization S :=
  E.graphSumRealization_iff_componentConnectedSumDecomposition.trans
    (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_sphericalGraphSumRealization

theorem graphSumRealization_of_graphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.graphSumFrontier S) : E.graphSumRealization :=
  E.graphSumRealization_of_componentConnectedSumDecomposition
    (E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
      ⟨h.1,
        E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
          (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr
            ((E.cutComponentCanonicalGluing_iff_sphericalSummandCompletion S hS).mpr h.2.1))
          (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr
            ((E.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined S hS).mpr
              h.2.2))⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_graphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_graphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_graphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_graphSumFrontier

theorem incidenceCycleRank_eq_zero_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    E.incidenceCycleRank C = 0 := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  refine (E.incidenceCycleRank_eq_zero_iff C).mpr ?_
  rw [hN, hC, Set.ncard_singleton]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty

theorem noTubeRealization_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.sphericalGraphSumRealization S) : E.NoTubeRealization :=
  E.noTubeRealization_iff_canonicalEnumeration.mpr fun C hC => by
    obtain ⟨ρ⟩ := h C
    rw [E.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty C hC] at ρ
    exact ⟨by simpa using ρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_sphericalGraphSumRealization

theorem sphericalSummandCompletion_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.sphericalGraphSumRealization S) : E.sphericalSummandCompletion S :=
  fun C _ => ⟨E.incidenceCycleRank C, h C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_sphericalGraphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_sphericalGraphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_sphericalGraphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_sphericalGraphSumRealization

theorem sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hr : E.NoTubeRealization) (h : E.cutGraphSumFrontier S) :
    E.sphericalGraphSumRealization S := by
  intro C
  by_cases hC : E.cutIndices C = ∅
  · have h0 := E.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty C hC
    have hρ := (E.noTubeRealization_iff_canonicalEnumeration.mp hr) C hC
    rw [h0]
    simpa using hρ
  · obtain ⟨b, hdiff⟩ := h.1 C hC
    rw [← h.2 C b hdiff]
    exact hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier

theorem sphericalGraphSumRealization_of_graphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.graphSumFrontier S) : E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_noTubeRealization_of_cutGraphSumFrontier
    S h.1 h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_graphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_graphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_graphSumFrontier ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalGraphSumRealization_of_graphSumFrontier

theorem graphSumFrontier_of_graphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.graphSumRealization) :
    E.NoTubeRealization ∧ E.sphericalSummandCompletion S :=
  ⟨E.noTubeRealization_of_componentConnectedSumDecomposition
      (E.componentConnectedSumDecomposition_of_graphSumRealization h),
    E.sphericalSummandCompletion_of_cutGraphSumRealization S hS
      (E.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization.mp h).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier_of_graphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier_of_graphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier_of_graphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumFrontier_of_graphSumRealization

theorem sphericalSummandCompletion_of_graphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.graphSumRealization) : E.sphericalSummandCompletion S :=
  (E.graphSumFrontier_of_graphSumRealization S hS h).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_graphSumRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_graphSumRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_graphSumRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_graphSumRealization

theorem orientedDiffeomorph_finiteConnectedSum_of_graphSumRealization_of_cutIndices_eq_empty
    (h : E.graphSumRealization) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) :=
  (E.noTubeRealization_iff_canonicalEnumeration.mp
    (E.noTubeRealization_of_componentConnectedSumDecomposition
      (E.componentConnectedSumDecomposition_of_graphSumRealization h))) C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.orientedDiffeomorph_finiteConnectedSum_of_graphSumRealization_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.orientedDiffeomorph_finiteConnectedSum_of_graphSumRealization_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.orientedDiffeomorph_finiteConnectedSum_of_graphSumRealization_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.orientedDiffeomorph_finiteConnectedSum_of_graphSumRealization_of_cutIndices_eq_empty

theorem graphSumRealization_iff_noTubeRealization_of_isEmpty_index [IsEmpty E.tubes.Index] :
    E.graphSumRealization ↔ E.NoTubeRealization :=
  ⟨fun h => E.noTubeRealization_of_componentConnectedSumDecomposition
      (E.componentConnectedSumDecomposition_of_graphSumRealization h),
    fun hr => E.graphSumRealization_of_isEmpty_index hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_noTubeRealization_of_isEmpty_index

theorem cutGraphSumRealization_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutGraphSumRealization :=
  fun C hC => absurd (h C) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutGraphSumRealization_of_forall_cutIndices_eq_empty

theorem sphericalSummandCompletion_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.sphericalSummandCompletion S :=
  fun C hC => absurd (h C) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_forall_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_forall_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_forall_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.sphericalSummandCompletion_of_forall_cutIndices_eq_empty

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_of_graphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : ∀ i : Fin T.eventCount, (T.transition i).graphSumFrontier S) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).graphSumRealization_iff_componentConnectedSumDecomposition.mp
    ((T.transition i).graphSumRealization_of_graphSumFrontier S hS (h i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_graphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_graphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_graphSumFrontier ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentConnectedSumDecomposition_of_graphSumFrontier

theorem sphericalGraphSumRealization_of_graphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ i : Fin T.eventCount, (T.transition i).graphSumFrontier S) :
    ∀ i : Fin T.eventCount, (T.transition i).sphericalGraphSumRealization S :=
  fun i => (T.transition i).sphericalGraphSumRealization_of_graphSumFrontier S (h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.sphericalGraphSumRealization_of_graphSumFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.sphericalGraphSumRealization_of_graphSumFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.sphericalGraphSumRealization_of_graphSumFrontier ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.sphericalGraphSumRealization_of_graphSumFrontier

end FiniteCutCapTrace

end DifferentialGeometry.Topology
