import Submission.DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer
import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationBlockCount
import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationSeam

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

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

private theorem connectedComponents_mk_map_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) {a b : α}
    (h : (a : ConnectedComponents α) = (b : ConnectedComponents α)) :
    (f a : ConnectedComponents β) = (f b : ConnectedComponents β) := by
  rw [ConnectedComponents.coe_eq_coe'] at h ⊢
  exact IsPreconnected.subset_connectedComponent
    (isPreconnected_connectedComponent.image f hf.continuousOn)
    ⟨b, mem_connectedComponent, rfl⟩ ⟨a, h, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.connectedComponents_mk_map_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.connectedComponents_mk_map_eq target :: scope.openDecls } }

private instance instPreconnectedSpaceSetIcc (a b : ℝ) : PreconnectedSpace (Set.Icc a b) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instPreconnectedSpaceSetIcc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instPreconnectedSpaceSetIcc target :: scope.openDecls } }

private instance instSubsingletonConnectedComponentsTube :
    Subsingleton (ConnectedComponents Tube) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instSubsingletonConnectedComponentsTube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instSubsingletonConnectedComponentsTube target :: scope.openDecls } }

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}}

theorem connectedComponents_mk_cylinderEnd {S : Finset G.Edge} {e : G.Edge}
    (P : PartialRealization G S) (he : e ∈ S) (h : P.SeamEquation e he) (b : Bool) (z : S²) :
    ConnectedComponents.mk (P.cylinderPiece e he (z, tubeEndLevel b)) =
      ConnectedComponents.mk
        (P.vertexPiece (G.endpoint e b) (G.flagBoundaryPoint S e b z)) := by
  cases b with
  | false => exact congrArg ConnectedComponents.mk (h.1 z)
  | true => exact congrArg ConnectedComponents.mk (h.2 z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_cylinderEnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_cylinderEnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_cylinderEnd ``Submission.DifferentialGeometry.Topology.PartialRealization.connectedComponents_mk_cylinderEnd

theorem exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece {S : Finset G.Edge}
    {e : G.Edge} (P : PartialRealization G S) (he : e ∈ S) (h : P.SeamEquation e he)
    (q : G.cylinderCarrier e) :
    ∃ (v : G.Vertex) (y : G.puncturedCarrier S v),
      ConnectedComponents.mk (P.cylinderPiece e he q) =
        ConnectedComponents.mk (P.vertexPiece v y) := by
  refine ⟨G.endpoint e _root_.Bool.false, G.flagBoundaryPoint S e _root_.Bool.false q.1, ?_⟩
  have hq : (q : ConnectedComponents (G.cylinderCarrier e)) =
      ((q.1, tubeEndLevel _root_.Bool.false) : ConnectedComponents (G.cylinderCarrier e)) :=
    Subsingleton.elim _ _
  rw [connectedComponents_mk_map_eq (P.cylinderPiece e he).continuous hq]
  exact connectedComponents_mk_cylinderEnd P he h _root_.Bool.false q.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece ``Submission.DifferentialGeometry.Topology.PartialRealization.exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece

def FlagCovered {S : Finset G.Edge} (P : PartialRealization G S) (e : G.Edge) : Prop :=
  ∀ x : P.realization.Carrier,
    (∃ (v : G.Vertex) (y : G.puncturedCarrier S v), P.vertexPiece v y = x) ∨
      (∃ (he : e ∈ S) (q : G.cylinderCarrier e), P.cylinderPiece e he q = x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagCovered ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagCovered

theorem cylinderComponentCovering_of_flagCovered_of_seamEquation {S : Finset G.Edge}
    {e : G.Edge} {P : PartialRealization G S} (he : e ∈ S) (hcover : P.FlagCovered e)
    (h : P.SeamEquation e he) : P.CylinderComponentCovering := by
  intro x
  rcases hcover x with ⟨v, y, hy⟩ | ⟨he', q, hq⟩
  · exact ⟨v, y, by rw [hy]⟩
  · obtain ⟨v, y, hC⟩ := exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece P he' h q
    exact ⟨v, y, by rw [← hq, hC]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_of_flagCovered_of_seamEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_of_flagCovered_of_seamEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_of_flagCovered_of_seamEquation ``Submission.DifferentialGeometry.Topology.PartialRealization.cylinderComponentCovering_of_flagCovered_of_seamEquation

theorem isBlockInvariant_of_flagCovered_of_seamEquation {S : Finset G.Edge} {e : G.Edge}
    {Z : ConnectedClosedOrientedManifold.{u} 3} {P : PartialRealization G S} (he : e ∈ S)
    (hcover : P.FlagCovered e) (h : P.SeamEquation e he) (hcorr : P.componentCorrespondence)
    (hpres : P.HasBlockPresentation Z) : P.IsBlockInvariant Z :=
  ⟨hcorr, hpres, cylinderComponentCovering_of_flagCovered_of_seamEquation he hcover h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation ``Submission.DifferentialGeometry.Topology.PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation

end PartialRealization

structure CollaredQuotientStep (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop where
  step : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsBlockInvariant Z →
      ∃ P' : PartialRealization G (_root_.Insert.insert e S),
        P'.FlagCovered e ∧ P'.SeamEquation e (Finset.mem_insert_self e S) ∧
          P'.componentCorrespondence ∧ P'.HasBlockPresentation Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CollaredQuotientStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CollaredQuotientStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CollaredQuotientStep ``Submission.DifferentialGeometry.Topology.CollaredQuotientStep

theorem hasRealizationStep_of_collaredQuotientStep {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : CollaredQuotientStep G Z) :
    HasRealizationStep G Z :=
  fun S P e he hP => by
    obtain ⟨P', hcover, hseam, hcorr, hpres⟩ := h.step S P e he hP
    exact ⟨P', PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation
      (Finset.mem_insert_self e S) hcover hseam hcorr hpres⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasRealizationStep_of_collaredQuotientStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasRealizationStep_of_collaredQuotientStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasRealizationStep_of_collaredQuotientStep ``Submission.DifferentialGeometry.Topology.hasRealizationStep_of_collaredQuotientStep

theorem blockStepLaw_of_collaredQuotientStep_of_initial {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h₀ : ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z)
    (h : CollaredQuotientStep G Z) : BlockStepLaw G Z :=
  blockStepLaw_of_hasRealizationStep_of_initial h₀ (hasRealizationStep_of_collaredQuotientStep h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.blockStepLaw_of_collaredQuotientStep_of_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.blockStepLaw_of_collaredQuotientStep_of_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.blockStepLaw_of_collaredQuotientStep_of_initial ``Submission.DifferentialGeometry.Topology.blockStepLaw_of_collaredQuotientStep_of_initial

theorem collaredQuotientStep_of_isEmpty {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} [IsEmpty G.Edge] :
    CollaredQuotientStep G Z :=
  ⟨fun _ _ e _ _ => isEmptyElim e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collaredQuotientStep_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collaredQuotientStep_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collaredQuotientStep_of_isEmpty ``Submission.DifferentialGeometry.Topology.collaredQuotientStep_of_isEmpty

theorem hasRealizationStep_of_isEmpty {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} [IsEmpty G.Edge] :
    HasRealizationStep G Z :=
  fun _ _ e _ _ => isEmptyElim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasRealizationStep_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasRealizationStep_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasRealizationStep_of_isEmpty ``Submission.DifferentialGeometry.Topology.hasRealizationStep_of_isEmpty

theorem collaredQuotientStep_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    CollaredQuotientStep (MarkedManifoldGraph.oneVertex N) Z :=
  collaredQuotientStep_of_isEmpty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collaredQuotientStep_oneVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collaredQuotientStep_oneVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collaredQuotientStep_oneVertex ``Submission.DifferentialGeometry.Topology.collaredQuotientStep_oneVertex

theorem collaredQuotientStep_twoVertexEmpty
    (N N' Z : ConnectedClosedOrientedManifold.{0} 3) :
    CollaredQuotientStep (MarkedManifoldGraph.twoVertexEmpty N N') Z :=
  collaredQuotientStep_of_isEmpty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.collaredQuotientStep_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.collaredQuotientStep_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.collaredQuotientStep_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.collaredQuotientStep_twoVertexEmpty

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {e : G.Edge}

theorem StepAssemblyData.partialRealization_flagCovered (D : StepAssemblyData G ∅ e) :
    (D.partialRealization).FlagCovered e := by
  intro x
  rcases D.partialRealization.covers x with ⟨v, y, hy⟩ | ⟨f, hf, q, hq⟩
  · exact Or.inl ⟨v, y, hy⟩
  · have hfe : f = e := by simpa using hf
    subst hfe
    exact Or.inr ⟨_, q, hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_flagCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_flagCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_flagCovered ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_flagCovered

theorem StepAssemblyData.partialRealization_isBlockInvariant
    {Z : ConnectedClosedOrientedManifold.{u} 3} (D : StepAssemblyData G ∅ e)
    (hcorr : (D.partialRealization).componentCorrespondence)
    (hpres : (D.partialRealization).HasBlockPresentation Z) :
    (D.partialRealization).IsBlockInvariant Z :=
  isBlockInvariant_of_flagCovered_of_seamEquation (Finset.mem_insert_self e ∅)
    D.partialRealization_flagCovered D.partialRealization_seamEquation hcorr hpres

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_isBlockInvariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_isBlockInvariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_isBlockInvariant ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_isBlockInvariant

end PartialRealization

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem not_stepAssemblyRel_cylinder_of_mem {S : Finset G.Edge} {e f : G.Edge}
    (he : e ∉ S) (hf : f ∈ S) (q : G.cylinderCarrier f) (y : G.assemblyCarrier (_root_.Insert.insert e S)) :
    ¬ G.stepAssemblyRel S e (Sum.inr ⟨⟨f, Finset.mem_insert_of_mem hf⟩, q⟩) y := by
  intro h
  have hne : f ≠ e := fun hfe => he (hfe ▸ hf)
  rcases h with ⟨z, hx, -⟩ | ⟨z, -, hx⟩ | ⟨z, hx, -⟩ | ⟨z, -, hx⟩
  · exact Sum.inr_ne_inl hx
  · exact hne (Subtype.ext_iff.mp (Sigma.mk.inj_iff.mp (Sum.inr.inj hx)).1)
  · exact hne (Subtype.ext_iff.mp (Sigma.mk.inj_iff.mp (Sum.inr.inj hx)).1)
  · exact Sum.inr_ne_inl hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.not_stepAssemblyRel_cylinder_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.not_stepAssemblyRel_cylinder_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.not_stepAssemblyRel_cylinder_of_mem ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.not_stepAssemblyRel_cylinder_of_mem

theorem vertexBlockList_length (S : Finset G.Edge) (v : G.Vertex) :
    (G.vertexBlockList S v).length = (G.vertexBlock S v).card := by
  rw [vertexBlockList, List.length_map, Finset.length_toList]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_length ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.vertexBlockList_length

def blockSummandCount (S : Finset G.Edge) (b : G.Vertex → ℕ) : Prop :=
  ∀ v : G.Vertex, b v + (G.vertexBlock S v).card = (G.blockEdgeFinset S v).card + 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount

theorem blockSummandCount_empty {b : G.Vertex → ℕ} :
    G.blockSummandCount (∅ : Finset G.Edge) b ↔ ∀ v : G.Vertex, b v = 0 := by
  constructor
  · intro h v
    have hv := h v
    rw [vertexBlock_empty, blockEdgeFinset, Finset.filter_empty, Finset.card_singleton,
      Finset.card_empty] at hv
    omega
  · intro h v
    rw [vertexBlock_empty, blockEdgeFinset, Finset.filter_empty, Finset.card_singleton,
      Finset.card_empty, h v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount_empty ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.blockSummandCount_empty

theorem eq_card_sub_of_blockSummandCount {S : Finset G.Edge} {b : G.Vertex → ℕ}
    (h : G.blockSummandCount S b) (v : G.Vertex) :
    b v = (G.blockEdgeFinset S v).card + 1 - (G.vertexBlock S v).card := by
  have hv := h v
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.eq_card_sub_of_blockSummandCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.eq_card_sub_of_blockSummandCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.eq_card_sub_of_blockSummandCount ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.eq_card_sub_of_blockSummandCount

end MarkedManifoldGraph

end DifferentialGeometry.Topology
