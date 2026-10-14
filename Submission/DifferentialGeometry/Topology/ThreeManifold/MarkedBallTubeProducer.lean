import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCap
import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationStepAssembly

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

local instance markedBallClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.markedBallClosedCellCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.markedBallClosedCellCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.markedBallClosedCellCharted ``Submission.DifferentialGeometry.Topology.markedBallClosedCellCharted
local instance markedBallClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.markedBallClosedCellIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.markedBallClosedCellIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.markedBallClosedCellIsManifold ``Submission.DifferentialGeometry.Topology.markedBallClosedCellIsManifold

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

def ofBallEmbedding (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) : MarkedBall N where
  ball := ball
  ball_embedding := ball_embedding
  collar := _root_.Set.univ
  collar_isOpen := isOpen_univ
  ball_subset_collar := Set.subset_univ (_root_.Set.range ball)
  collarBudget := 1
  collarBudget_pos := one_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding ``Submission.DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding

theorem ofBallEmbedding_ball (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) :
    (ofBallEmbedding ball ball_embedding).ball = ball := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_ball ``Submission.DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_ball

theorem ofBallEmbedding_collar (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) :
    (ofBallEmbedding ball ball_embedding).collar = univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collar ``Submission.DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collar

theorem ofBallEmbedding_collarBudget (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) :
    (ofBallEmbedding ball ball_embedding).collarBudget = 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collarBudget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collarBudget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collarBudget ``Submission.DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding_collarBudget

theorem nonempty_iff_exists_isSmoothEmbedding :
    Nonempty (MarkedBall N) ↔
      ∃ ball : ClosedCell 3 → N.Carrier,
        IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball :=
  ⟨fun ⟨B⟩ => ⟨B.ball, B.ball_embedding⟩,
    fun ⟨ball, hball⟩ => ⟨ofBallEmbedding ball hball⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.nonempty_iff_exists_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.nonempty_iff_exists_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.nonempty_iff_exists_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.MarkedBall.nonempty_iff_exists_isSmoothEmbedding

theorem collar_nonempty (B : MarkedBall N) : B.collar.Nonempty :=
  ⟨B.ball (closedCellCenter 3),
    B.ball_subset_collar (_root_.Set.mem_range_self (closedCellCenter 3))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.collar_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.collar_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.collar_nonempty ``Submission.DifferentialGeometry.Topology.MarkedBall.collar_nonempty

theorem collar_ne_univ_of_disjoint (B : MarkedBall N) {C : Set N.Carrier}
    (h : Disjoint B.collar C) (hC : C.Nonempty) : B.collar ≠ univ := by
  intro hc
  obtain ⟨x, hx⟩ := hC
  exact Set.disjoint_left.mp h (by simp [hc]) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.collar_ne_univ_of_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.collar_ne_univ_of_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.collar_ne_univ_of_disjoint ``Submission.DifferentialGeometry.Topology.MarkedBall.collar_ne_univ_of_disjoint

theorem not_disjoint_of_collar_eq_univ (B B' : MarkedBall N) (h : B.collar = _root_.Set.univ) :
    ¬ Disjoint B.collar B'.collar :=
  fun hd => collar_ne_univ_of_disjoint B hd B'.collar_nonempty h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.not_disjoint_of_collar_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.not_disjoint_of_collar_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.not_disjoint_of_collar_eq_univ ``Submission.DifferentialGeometry.Topology.MarkedBall.not_disjoint_of_collar_eq_univ

end MarkedBall

namespace SphericalCapping

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}

def markedBall (E : SphericalCapping M N T) (b : T.Boundary) : MarkedBall N :=
  MarkedBall.ofBallEmbedding (E.cap b) (E.cap_embedding b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.markedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.markedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.markedBall ``Submission.DifferentialGeometry.Topology.SphericalCapping.markedBall

theorem markedBall_ball (E : SphericalCapping M N T) (b : T.Boundary) :
    (markedBall E b).ball = E.cap b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.markedBall_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.markedBall_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.markedBall_ball ``Submission.DifferentialGeometry.Topology.SphericalCapping.markedBall_ball

theorem markedBall_collar (E : SphericalCapping M N T) (b : T.Boundary) :
    (markedBall E b).collar = univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.markedBall_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.markedBall_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.markedBall_collar ``Submission.DifferentialGeometry.Topology.SphericalCapping.markedBall_collar

theorem nonempty_markedBall_of_boundary (E : SphericalCapping M N T)
    (h : Nonempty T.Boundary) : Nonempty (MarkedBall N) :=
  h.elim fun b => ⟨markedBall E b⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.nonempty_markedBall_of_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.nonempty_markedBall_of_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.nonempty_markedBall_of_boundary ``Submission.DifferentialGeometry.Topology.SphericalCapping.nonempty_markedBall_of_boundary

end SphericalCapping

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem nonempty_markedBall_of_tube (h : Nonempty E.tubes.Index) : Nonempty (MarkedBall E.capped) :=
  h.elim fun a => ⟨SphericalCapping.markedBall E.capping (a, _root_.Bool.false)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.nonempty_markedBall_of_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.nonempty_markedBall_of_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.nonempty_markedBall_of_tube ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.nonempty_markedBall_of_tube

end SphericalCutCapTransition

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

private theorem set_nonempty_cast {V : Type u} (X : V → Type u) {a b : V} (h : a = b)
    {S : Set (X a)} (hS : S.Nonempty) : (h ▸ S : Set (X b)).Nonempty := by
  cases h
  exact hS

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.set_nonempty_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.MarkedManifoldGraph.set_nonempty_cast target :: scope.openDecls } }

theorem flag_collar_ne_univ_of_ne (e e' : G.Edge) (b b' : Bool)
    (hv : G.endpoint e' b' = G.endpoint e b) (h : (e, b) ≠ (e', b')) :
    (G.flag e b).collar ≠ univ := by
  classical
  have hne : (⟨(e, b), rfl⟩ : {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
      ⟨(e', b'), hv⟩ := fun hh => h (congrArg Subtype.val hh)
  have hdisj : Disjoint (G.flag e b).collar (hv ▸ (G.flag e' b').collar) := by
    simpa using G.flag_collar_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv⟩ hne
  exact MarkedBall.collar_ne_univ_of_disjoint (G.flag e b) hdisj
    (set_nonempty_cast (fun v => (G.vertexManifold v).Carrier) hv (G.flag e' b').collar_nonempty)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flag_collar_ne_univ_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flag_collar_ne_univ_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flag_collar_ne_univ_of_ne ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flag_collar_ne_univ_of_ne

end MarkedManifoldGraph

def HasRealizationStep (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsBlockInvariant Z → ∃ P' : PartialRealization G (_root_.Insert.insert e S), P'.IsBlockInvariant Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HasRealizationStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HasRealizationStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HasRealizationStep ``Submission.DifferentialGeometry.Topology.HasRealizationStep

theorem hasRealizationStep_of_blockStepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : BlockStepLaw G Z) :
    HasRealizationStep G Z := h.step

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasRealizationStep_of_blockStepLaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasRealizationStep_of_blockStepLaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasRealizationStep_of_blockStepLaw ``Submission.DifferentialGeometry.Topology.hasRealizationStep_of_blockStepLaw

theorem blockStepLaw_of_hasRealizationStep_of_initial {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h₀ : ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z)
    (h : HasRealizationStep G Z) : BlockStepLaw G Z := ⟨h₀, h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.blockStepLaw_of_hasRealizationStep_of_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.blockStepLaw_of_hasRealizationStep_of_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.blockStepLaw_of_hasRealizationStep_of_initial ``Submission.DifferentialGeometry.Topology.blockStepLaw_of_hasRealizationStep_of_initial

theorem hasRealizationStep_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    HasRealizationStep (MarkedManifoldGraph.oneVertex N) Z :=
  hasRealizationStep_of_blockStepLaw (MarkedManifoldGraph.oneVertexBlockStepLaw N Z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasRealizationStep_oneVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasRealizationStep_oneVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasRealizationStep_oneVertex ``Submission.DifferentialGeometry.Topology.hasRealizationStep_oneVertex

theorem hasRealizationStep_twoVertexEmpty
    (N N' Z : ConnectedClosedOrientedManifold.{0} 3) :
    HasRealizationStep (MarkedManifoldGraph.twoVertexEmpty N N') Z :=
  fun _ _ e _ _ => PEmpty.elim e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasRealizationStep_twoVertexEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasRealizationStep_twoVertexEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasRealizationStep_twoVertexEmpty ``Submission.DifferentialGeometry.Topology.hasRealizationStep_twoVertexEmpty

end DifferentialGeometry.Topology
