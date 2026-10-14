import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

private theorem forall₂_replicate_of_forall_mem {α : Type*} (P : α → α → Prop) {S : α} :
    ∀ {L : List α}, (∀ F ∈ L, P F S) → List.Forall₂ P L (List.replicate L.length S)
  | [], _ => by simp
  | a :: t, h => by
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp))
      (forall₂_replicate_of_forall_mem P fun F hF => h F (by simp [hF]))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.forall₂_replicate_of_forall_mem target :: scope.openDecls } }

theorem nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor
    {F S : ConnectedClosedOrientedManifold.{u} 3}
    (hF : isSphereTwoTimesCircleFactor F) (hS : isSphereTwoTimesCircleFactor S) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph F.toClosedOrientedManifold
      S.toClosedOrientedManifold) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨s, hs⟩ := hS
  exact ⟨⟨f.trans s.symm,
    Diffeomorph.preservesOrientation_trans hf (Diffeomorph.preservesOrientation_symm hs)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem componentConnectedSumDecomposition_iff_fixedSphericalModel
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.componentConnectedSumDecomposition ↔
      ∀ (C : ConnectedComponents M.Carrier)
        (L : List (ConnectedClosedOrientedManifold.{u} 3)) (b : ℕ),
        E.CompleteEnumeration C L →
        b + L.length = (E.cutIndices C).card + 1 →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ List.replicate b S)).toClosedOrientedManifold) := by
  classical
  have hle : ∀ {C : ConnectedComponents M.Carrier}
      {L : List (ConnectedClosedOrientedManifold.{u} 3)},
      E.CompleteEnumeration C L → L.length ≤ (E.cutIndices C).card + 1 := by
    intro C L hL
    have h1 := E.ncard_associatedFactors_le_card_cutIndices_add_one C
    have h2 := E.ncard_associatedFactors_eq_length hL
    omega
  constructor
  · intro h C L b hL hb
    obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C L hL
    have hbK : b = K.length := by
      have := hle hL
      omega
    subst hbK
    have hLL : List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          A.toClosedOrientedManifold B.toClosedOrientedManifold)) L L :=
      List.forall₂_same.mpr fun A _ => ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
    have hKrep : List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          A.toClosedOrientedManifold B.toClosedOrientedManifold))
        K (List.replicate K.length S) :=
      forall₂_replicate_of_forall_mem _
        (fun F hF => nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor
          (hKfac F hF) hS)
    have hcongr := finiteConnectedSum_congr_of_connectedSumLaws
      (connectedSumLaws_of_associative connectedSumAssociative_holds)
      (List.rel_append hLL hKrep)
    obtain ⟨ρ⟩ := hdiff
    obtain ⟨σ⟩ := hcongr
    exact ⟨ρ.trans σ⟩
  · intro h C L hL
    refine ⟨List.replicate ((E.cutIndices C).card + 1 - L.length) S, ?_, ?_, ?_⟩
    · simp
    · intro F hF
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
      exact hS
    · exact h C L _ hL (by have := hle hL; omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_fixedSphericalModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_fixedSphericalModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_fixedSphericalModel ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_fixedSphericalModel

theorem componentConnectedSumDecomposition_iff_sphereTwoTimesCircleLift
    {M Q : ClosedOrientedManifold.{0} 3} (E : SphericalCutCapTransition M Q) :
    E.componentConnectedSumDecomposition ↔
      ∀ (C : ConnectedComponents M.Carrier)
        (L : List (ConnectedClosedOrientedManifold.{0} 3)) (b : ℕ),
        E.CompleteEnumeration C L →
        b + L.length = (E.cutIndices C).card + 1 →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ List.replicate b sphereTwoTimesCircleLift)).toClosedOrientedManifold) :=
  E.componentConnectedSumDecomposition_iff_fixedSphericalModel sphereTwoTimesCircleLift
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_sphereTwoTimesCircleLift

end SphericalCutCapTransition

end DifferentialGeometry.Topology
