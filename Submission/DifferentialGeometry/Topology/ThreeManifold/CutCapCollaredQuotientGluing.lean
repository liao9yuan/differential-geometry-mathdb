import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentGluingReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapUncutCappingRealization
import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationStepQuotient
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

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

structure CutComponentCollaredQuotientRealization : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ N : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientRealization

theorem cutComponentCollaredQuotientRealization_of_self :
    E.CutComponentCollaredQuotientRealization :=
  ⟨fun C _ => ⟨M.component C, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_self ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_self

theorem cutComponentCollaredQuotientRealization_of_cutComponentGluing :
    E.cutComponentGluing → E.CutComponentCollaredQuotientRealization :=
  fun _ => E.cutComponentCollaredQuotientRealization_of_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_cutComponentGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_cutComponentGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_cutComponentGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_cutComponentGluing

theorem not_collaredQuotientRealization_determines_blockLength :
    ¬ (∀ (N : ConnectedClosedOrientedManifold.{u} 3)
      (K K' : List (ConnectedClosedOrientedManifold.{u} 3)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold (finiteConnectedSum K).toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold (finiteConnectedSum K').toClosedOrientedManifold) →
      K.length = K'.length) := by
  intro h
  have hlen := h standardThreeSphereLift.{u} [standardThreeSphereLift.{u}] []
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  simp only [List.length_singleton, List.length_nil] at hlen
  exact absurd hlen (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.not_collaredQuotientRealization_determines_blockLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.not_collaredQuotientRealization_determines_blockLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.not_collaredQuotientRealization_determines_blockLength ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.not_collaredQuotientRealization_determines_blockLength

structure CutComponentSingleTubeCollaredQuotientGluing : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), (E.cutIndices C).card = 1 →
    ∃ (N : ConnectedClosedOrientedManifold.{u} 3)
      (K : List (ConnectedClosedOrientedManifold.{u} 3)),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentSingleTubeCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentSingleTubeCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentSingleTubeCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentSingleTubeCollaredQuotientGluing

theorem cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing
    (h : E.CutComponentSingleTubeCollaredQuotientGluing) :
    E.cutComponentSingleTubeGluing := by
  intro C hcard
  obtain ⟨N, K, hKfac, ⟨ρ₁⟩, ⟨ρ₂⟩⟩ := h.quotient C hcard
  exact ⟨K, hKfac, ⟨ρ₁.trans ρ₂⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing

structure CutComponentCollaredQuotientGluing : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ (N : ConnectedClosedOrientedManifold.{u} 3)
        (K : List (ConnectedClosedOrientedManifold.{u} 3)),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          N.toClosedOrientedManifold (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluing

theorem cutComponentGluing_of_cutComponentCollaredQuotientGluing
    (h : E.CutComponentCollaredQuotientGluing) : E.cutComponentGluing := by
  intro C hC L hL
  obtain ⟨N, K, hKfac, ⟨ρ₁⟩, ⟨ρ₂⟩⟩ := h.quotient C hC L hL
  exact ⟨K, hKfac, ⟨ρ₁.trans ρ₂⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluing

theorem cutComponentCollaredQuotientGluing_of_cutComponentGluing
    (h : E.cutComponentGluing) : E.CutComponentCollaredQuotientGluing := by
  refine ⟨fun C hC L hL => ?_⟩
  obtain ⟨K, hKfac, ⟨ρ⟩⟩ := h C hC L hL
  exact ⟨M.component C, K, hKfac,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩, ⟨ρ⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentGluing

theorem cutComponentGluing_iff_cutComponentCollaredQuotientGluing :
    E.cutComponentGluing ↔ E.CutComponentCollaredQuotientGluing :=
  ⟨E.cutComponentCollaredQuotientGluing_of_cutComponentGluing,
    E.cutComponentGluing_of_cutComponentCollaredQuotientGluing⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_iff_cutComponentCollaredQuotientGluing

theorem cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    (h : E.CutComponentCollaredQuotientGluing) :
    E.CutComponentSingleTubeCollaredQuotientGluing := by
  refine ⟨fun C hcard => ?_⟩
  have hC : E.cutIndices C ≠ ∅ := by
    rintro h0
    rw [h0] at hcard
    simp at hcard
  exact h.quotient C hC (E.canonicalEnumeration C)
    (E.completeEnumeration_canonicalEnumeration C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing

theorem cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing
    (h : E.cutComponentGluing) : E.CutComponentSingleTubeCollaredQuotientGluing :=
  E.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    (E.cutComponentCollaredQuotientGluing_of_cutComponentGluing h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing

theorem cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index
    [Subsingleton E.tubes.Index] (h : E.CutComponentSingleTubeCollaredQuotientGluing) :
    E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentSingleTubeGluing_of_subsingleton_index
    (E.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index

theorem cutComponentCollaredQuotientGluing_of_isEmpty_index [IsEmpty E.tubes.Index] :
    E.CutComponentCollaredQuotientGluing :=
  E.cutComponentCollaredQuotientGluing_of_cutComponentGluing
    (E.cutComponentGluing_of_forall_cutIndices_eq_empty fun C =>
      E.cutIndices_eq_empty_of_isEmpty_index C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_isEmpty_index

theorem cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index
    [IsEmpty E.tubes.Index] : E.CutComponentSingleTubeCollaredQuotientGluing :=
  E.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    E.cutComponentCollaredQuotientGluing_of_isEmpty_index

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index

theorem cutComponentCollaredQuotientRealization_of_isEmpty_index [IsEmpty E.tubes.Index] :
    E.CutComponentCollaredQuotientRealization :=
  E.cutComponentCollaredQuotientRealization_of_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientRealization_of_isEmpty_index

structure CutComponentCollaredQuotientGluingBridge where
  graph : MarkedManifoldGraph.{u}
  zFactor : ConnectedClosedOrientedManifold.{u} 3
  zFactor_sphere : isSphereTwoTimesCircleFactor zFactor
  realized : PartialRealization graph Finset.univ
  realized_blockInvariant : realized.IsBlockInvariant zFactor
  vertexOf : ConnectedComponents M.Carrier → graph.Vertex
  blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
    E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C))
  componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
    (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (realized.realization.component
          (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluingBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluingBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluingBridge ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CutComponentCollaredQuotientGluingBridge

theorem cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) :
    E.CutComponentCollaredQuotientGluing := by
  obtain ⟨b, -, hb⟩ := h.realized_blockInvariant.2.1
  refine ⟨fun C _ L hL => ?_⟩
  obtain ⟨y⟩ := MarkedManifoldGraph.nonempty_puncturedCarrier h.graph Finset.univ (h.vertexOf C)
  refine ⟨h.realized.realization.component
      (ConnectedComponents.mk (h.realized.vertexPiece (h.vertexOf C) y)),
    List.replicate (b (h.vertexOf C)) h.zFactor, ?_, h.componentDiffeo C y, ?_⟩
  · intro F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact h.zFactor_sphere
  · obtain ⟨ρ₂⟩ := hb (h.vertexOf C) y
    obtain ⟨ρ₃⟩ := finiteConnectedSum_perm
      ((E.completeEnumeration_perm (h.blockEnumeration C) hL).append_right
        (List.replicate (b (h.vertexOf C)) h.zFactor))
    exact ⟨ρ₂.trans ρ₃⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge

theorem cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) : E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentCollaredQuotientGluing
    (E.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge

def cutComponentCollaredQuotientGluingBridge_of_seamData
    (graph : MarkedManifoldGraph.{u}) (zFactor : ConnectedClosedOrientedManifold.{u} 3)
    (zFactor_sphere : isSphereTwoTimesCircleFactor zFactor)
    (realized : PartialRealization graph Finset.univ)
    {e : graph.Edge} (he : e ∈ (Finset.univ : Finset graph.Edge))
    (hcover : realized.FlagCovered e) (hseam : realized.SeamEquation e he)
    (hcorr : realized.componentCorrespondence) (hpres : realized.HasBlockPresentation zFactor)
    (vertexOf : ConnectedComponents M.Carrier → graph.Vertex)
    (blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
      E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C)))
    (componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
      (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (realized.realization.component
            (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)) :
    E.CutComponentCollaredQuotientGluingBridge :=
  ⟨graph, zFactor, zFactor_sphere, realized,
    PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation he hcover hseam hcorr hpres,
    vertexOf, blockEnumeration, componentDiffeo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluingBridge_of_seamData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluingBridge_of_seamData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluingBridge_of_seamData ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentCollaredQuotientGluingBridge_of_seamData

theorem cutComponentGluing_of_seamData
    (graph : MarkedManifoldGraph.{u}) (zFactor : ConnectedClosedOrientedManifold.{u} 3)
    (zFactor_sphere : isSphereTwoTimesCircleFactor zFactor)
    (realized : PartialRealization graph Finset.univ)
    {e : graph.Edge} (he : e ∈ (Finset.univ : Finset graph.Edge))
    (hcover : realized.FlagCovered e) (hseam : realized.SeamEquation e he)
    (hcorr : realized.componentCorrespondence) (hpres : realized.HasBlockPresentation zFactor)
    (vertexOf : ConnectedComponents M.Carrier → graph.Vertex)
    (blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
      E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C)))
    (componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
      (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (realized.realization.component
            (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)) :
    E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge
    (E.cutComponentCollaredQuotientGluingBridge_of_seamData graph zFactor zFactor_sphere
      realized he hcover hseam hcorr hpres vertexOf blockEnumeration componentDiffeo)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_seamData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_seamData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_seamData ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutComponentGluing_of_seamData

theorem componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    E.noTubeRealization (E.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge h) hcount

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge

end SphericalCutCapTransition

end DifferentialGeometry.Topology
