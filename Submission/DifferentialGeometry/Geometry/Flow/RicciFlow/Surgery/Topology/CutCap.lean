import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Relation
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeBall := Metric.closedBall (0 : ThreeSpace) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall


def sphereToThreeBall : C(Sphere 2, ThreeBall) :=
  ⟨fun x => ⟨x.1, le_of_eq x.2⟩, continuous_subtype_val.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereToThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereToThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereToThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereToThreeBall


abbrev TubeDomain := Sphere 2 × _root_.Set.Icc (-2 : ℝ) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain


structure TubeSystem (M : Type*) [TopologicalSpace M] where

  Index : Type
  finiteIndex : Fintype Index

  tube : Index → C(TubeDomain, M)
  embedding : ∀ a, Topology.IsEmbedding (tube a)
  disjoint : Pairwise fun a b => Disjoint (Set.range (tube a)) (Set.range (tube b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

attribute [instance] TubeSystem.finiteIndex

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)


def removedBand (a : T.Index) : Set M :=
  T.tube a '' {z : TubeDomain | (-1 : ℝ) < z.2.1 ∧ z.2.1 < 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.removedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.removedBand


def core : Set M := (⋃ a, T.removedBand a)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core


abbrev Boundary := T.Index × Bool

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.Boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.Boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.Boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.Boundary


def boundaryLevel (b : Bool) : _root_.Set.Icc (-2 : ℝ) 2 :=
  if b then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundaryLevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundaryLevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundaryLevel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundaryLevel


def boundarySphere (b : T.Boundary) : C(Sphere 2, M) :=
  (T.tube b.1).comp ⟨fun y => (y, boundaryLevel b.2), continuous_id.prodMk continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere

theorem boundarySphere_mem_core (b : T.Boundary) (y : Sphere 2) :
    T.boundarySphere b y ∈ T.core := by
  intro hm
  obtain ⟨a, z, hz, heq⟩ := by
    simpa only [_root_.Set.mem_iUnion, removedBand, _root_.Set.mem_image] using hm
  have ha : a = b.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne)
      (Set.mem_range_self z) ⟨(y, boundaryLevel b.2), heq.symm⟩
  subst a
  have hcoord := congrArg (fun z : TubeDomain => (z.2 : ℝ))
    ((T.embedding b.1).injective heq)
  rcases b with ⟨b, side⟩
  cases side <;> simp [boundaryLevel] at hcoord <;> rcases hz with ⟨hlo, hhi⟩ <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_core


def coreBoundarySphere (b : T.Boundary) : C(Sphere 2, T.core) :=
  ⟨fun y => ⟨T.boundarySphere b y, T.boundarySphere_mem_core b y⟩,
    (T.boundarySphere b).continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere

theorem core_eq_univ_of_isEmpty [IsEmpty T.Index] : T.core = univ := by
  simp [core]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core_eq_univ_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core_eq_univ_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core_eq_univ_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.core_eq_univ_of_isEmpty

end TubeSystem


abbrev ComponentCarrier {X : Type*} [TopologicalSpace X] (c : ConnectedComponents X) :=
  {x : X // ConnectedComponents.mk x = c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ComponentCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ComponentCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ComponentCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ComponentCarrier


structure Capping {M : Type*} [TopologicalSpace M] (T : TubeSystem M)
    (N : Type*) [TopologicalSpace N] where
  coreInclusion : C(T.core, N)
  coreEmbedding : Topology.IsEmbedding coreInclusion
  cap : T.Boundary → C(ThreeBall, N)
  capEmbedding : ∀ b, Topology.IsEmbedding (cap b)

  attaching : T.Boundary → Sphere 2 ≃ₜ Sphere 2
  boundary_eq : ∀ b y,
    cap b (sphereToThreeBall y) = coreInclusion (T.coreBoundarySphere b (attaching b y))
  exhaustive : Set.range coreInclusion ∪ (⋃ b, Set.range (cap b)) = _root_.Set.univ
  core_cap_intersection : ∀ b,
    Set.range coreInclusion ∩ Set.range (cap b) =
      Set.range (coreInclusion.comp (T.coreBoundarySphere b))
  cap_disjoint : Pairwise fun b b' => Disjoint (Set.range (cap b)) (Set.range (cap b'))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping

namespace Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {T : TubeSystem M} (K : Capping T N)


def componentMap : ConnectedComponents T.core → ConnectedComponents N :=
  K.coreInclusion.continuous.connectedComponentsMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap

@[simp] theorem componentMap_mk (x : T.core) :
    K.componentMap (ConnectedComponents.mk x) = ConnectedComponents.mk (K.coreInclusion x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentMap_mk

private noncomputable def spherePoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.spherePoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.spherePoint target :: scope.openDecls } }

private theorem coreBoundary_preconnected (b : T.Boundary) :
    IsPreconnected (_root_.Set.range (T.coreBoundarySphere b)) := by
  have : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  exact isPreconnected_range (T.coreBoundarySphere b).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreBoundary_preconnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreBoundary_preconnected target :: scope.openDecls } }

private noncomputable def capComponent (b : T.Boundary) : ConnectedComponents T.core :=
  ConnectedComponents.mk (T.coreBoundarySphere b spherePoint)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capComponent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capComponent target :: scope.openDecls } }

private theorem coreBoundary_subset_fiber (b : T.Boundary) :
    _root_.Set.range (T.coreBoundarySphere b) ⊆
      {z : T.core | ConnectedComponents.mk z = capComponent (T := T) b} := by
  intro z hz
  exact ConnectedComponents.coe_eq_coe'.mpr
    ((coreBoundary_preconnected (T := T) b).subset_connectedComponent
      (⟨spherePoint, rfl⟩ :
        (T.coreBoundarySphere b) spherePoint ∈ _root_.Set.range (T.coreBoundarySphere b)) hz)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreBoundary_subset_fiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreBoundary_subset_fiber target :: scope.openDecls } }

private theorem capRange_preconnected (b : T.Boundary) :
    IsPreconnected (_root_.Set.range (K.cap b)) := by
  have : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  exact isPreconnected_range (K.cap b).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capRange_preconnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capRange_preconnected target :: scope.openDecls } }

private noncomputable def piece (D : ConnectedComponents T.core) : Set N :=
  K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D} ∪
    ⋃ (b : {b : T.Boundary // capComponent (T := T) b = D}), _root_.Set.range (K.cap b.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece target :: scope.openDecls } }

private noncomputable def pieceAux (D : ConnectedComponents T.core) :
    Option {b : T.Boundary // capComponent (T := T) b = D} → Set N
  | none => K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D}
  | some b => _root_.Set.range (K.cap b.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pieceAux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pieceAux target :: scope.openDecls } }

private theorem cap_range_subset_piece (b : T.Boundary) :
    range (K.cap b) ⊆ piece K (capComponent (T := T) b) := by
  intro n hn
  exact Or.inr (mem_iUnion.mpr ⟨⟨b, rfl⟩, hn⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.cap_range_subset_piece
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.cap_range_subset_piece target :: scope.openDecls } }

private theorem coreInclusion_mem_piece_iff {D : ConnectedComponents T.core} {z : T.core} :
    K.coreInclusion z ∈ piece K D ↔ ConnectedComponents.mk z = D := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨w, hw, hwz⟩ := h
      have hwz' : w = z := K.coreEmbedding.injective hwz
      rw [← hwz']
      exact hw
    · obtain ⟨⟨b, hb⟩, hbn⟩ := mem_iUnion.mp h
      have hmem : K.coreInclusion z ∈ _root_.Set.range K.coreInclusion ∩ _root_.Set.range (K.cap b) :=
        ⟨⟨z, rfl⟩, hbn⟩
      rw [K.core_cap_intersection b] at hmem
      obtain ⟨y, hy⟩ := hmem
      have hy' : T.coreBoundarySphere b y = z := K.coreEmbedding.injective hy
      have hz' : ConnectedComponents.mk z = capComponent (T := T) b := by
        rw [← hy']
        exact coreBoundary_subset_fiber (T := T) b ⟨y, rfl⟩
      rw [hz', hb]
  · intro hz
    exact Or.inl ⟨z, hz, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreInclusion_mem_piece_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.coreInclusion_mem_piece_iff target :: scope.openDecls } }

private theorem corePart_preconnected (D : ConnectedComponents T.core) :
    IsPreconnected (K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = D}) := by
  obtain ⟨z₀, rfl⟩ := ConnectedComponents.surjective_coe D
  have hset : {z : T.core | ConnectedComponents.mk z = ConnectedComponents.mk z₀} =
      connectedComponent z₀ := connectedComponents_preimage_singleton
  rw [hset]
  exact isPreconnected_connectedComponent.image _ K.coreInclusion.continuous.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.corePart_preconnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.corePart_preconnected target :: scope.openDecls } }

private theorem boundaryPoint_mem_corePart (b : T.Boundary) :
    K.coreInclusion (T.coreBoundarySphere b (K.attaching b spherePoint)) ∈
      K.coreInclusion '' {z : T.core | ConnectedComponents.mk z = capComponent (T := T) b} :=
  ⟨_, coreBoundary_subset_fiber (T := T) b ⟨K.attaching b spherePoint, rfl⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.boundaryPoint_mem_corePart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.boundaryPoint_mem_corePart target :: scope.openDecls } }

private theorem boundaryPoint_mem_capRange (b : T.Boundary) :
    K.coreInclusion (T.coreBoundarySphere b (K.attaching b spherePoint)) ∈ _root_.Set.range (K.cap b) :=
  ⟨sphereToThreeBall spherePoint, K.boundary_eq b spherePoint⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.boundaryPoint_mem_capRange
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.boundaryPoint_mem_capRange target :: scope.openDecls } }

private theorem pieceAux_link (D : ConnectedComponents T.core)
    (b : {b : T.Boundary // capComponent (T := T) b = D}) :
    (pieceAux K D _root_.Option.none ∩ pieceAux K D (_root_.Option.some b)).Nonempty := by
  refine ⟨K.coreInclusion (T.coreBoundarySphere b.1 (K.attaching b.1 spherePoint)), ?_, ?_⟩
  · refine ⟨T.coreBoundarySphere b.1 (K.attaching b.1 spherePoint), ?_, rfl⟩
    exact (coreBoundary_subset_fiber (T := T) b.1
      ⟨K.attaching b.1 spherePoint, rfl⟩).trans b.2
  · exact boundaryPoint_mem_capRange K b.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pieceAux_link
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pieceAux_link target :: scope.openDecls } }

private theorem piece_preconnected (D : ConnectedComponents T.core) :
    IsPreconnected (piece K D) := by
  have hunion : (⋃ i, pieceAux K D i) = piece K D := by
    rw [_root_.Set.iUnion_option, piece]
    simp only [pieceAux]
  have hlink : ∀ i j, _root_.Relation.ReflTransGen
      (fun i j => (pieceAux K D i ∩ pieceAux K D j).Nonempty) i j := by
    intro i j
    match i, j with
    | none, _root_.Option.none => exact ReflTransGen.refl
    | none, _root_.Option.some b => exact ReflTransGen.single (pieceAux_link K D b)
    | some b, _root_.Option.none =>
      obtain ⟨x, hx⟩ := pieceAux_link K D b
      exact ReflTransGen.single ⟨x, hx.2, hx.1⟩
    | some b, _root_.Option.some b' =>
      obtain ⟨x, hx⟩ := pieceAux_link K D b
      exact (ReflTransGen.single (show (pieceAux K D (_root_.Option.some b) ∩
        pieceAux K D _root_.Option.none).Nonempty from ⟨x, hx.2, hx.1⟩)).tail (pieceAux_link K D b')
  have hpc : IsPreconnected (⋃ i, pieceAux K D i) :=
    IsPreconnected.iUnion_of_reflTransGen
      (fun i => by cases i with
        | none => exact corePart_preconnected K D
        | some b => exact capRange_preconnected K b.1) hlink
  rwa [hunion] at hpc

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_preconnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_preconnected target :: scope.openDecls } }

private theorem piece_isClosed [CompactSpace T.core] [T2Space N]
    (D : ConnectedComponents T.core) : IsClosed (piece K D) := by
  obtain ⟨z₀, rfl⟩ := ConnectedComponents.surjective_coe D
  have hset : {z : T.core | ConnectedComponents.mk z = ConnectedComponents.mk z₀} =
      connectedComponent z₀ := connectedComponents_preimage_singleton
  have hcore : IsClosed (K.coreInclusion '' {z : T.core |
      ConnectedComponents.mk z = ConnectedComponents.mk z₀}) := by
    rw [hset]
    exact (IsCompact.image (isClosed_connectedComponent).isCompact
      K.coreInclusion.continuous).isClosed
  have hfin : ({b : T.Boundary | capComponent (T := T) b = ConnectedComponents.mk z₀}).Finite :=
    Set.toFinite _
  have hcaps : IsClosed (⋃ b ∈
      {b : T.Boundary | capComponent (T := T) b = ConnectedComponents.mk z₀},
      range (K.cap b)) := by
    refine hfin.isClosed_biUnion ?_
    intro b _
    exact (isCompact_range (K.cap b).continuous).isClosed
  rw [piece]
  refine hcore.union ?_
  rw [_root_.Set.iUnion_subtype]
  exact hcaps

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_isClosed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_isClosed target :: scope.openDecls } }

private theorem piece_cover : ⋃ D, piece K D = univ := by
  refine _root_.Set.eq_univ_of_forall ?_
  intro n
  have hn : n ∈ _root_.Set.range K.coreInclusion ∪ ⋃ b, _root_.Set.range (K.cap b) := by
    rw [K.exhaustive]
    trivial
  rcases hn with hn | hn
  · obtain ⟨z, rfl⟩ := hn
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk z,
      (coreInclusion_mem_piece_iff K).mpr rfl⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨capComponent (T := T) b, cap_range_subset_piece K b hb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_cover target :: scope.openDecls } }

private theorem piece_pairwise_disjoint : Pairwise (Disjoint on piece K) := by
  intro D D' hne
  rw [Function.onFun, _root_.Set.disjoint_left]
  intro n hn hn'
  by_cases hcore : n ∈ _root_.Set.range K.coreInclusion
  · obtain ⟨z, rfl⟩ := hcore
    exact hne (((coreInclusion_mem_piece_iff K).mp hn).symm.trans
      ((coreInclusion_mem_piece_iff K).mp hn'))
  · have hnuc : n ∈ ⋃ (b : {b : T.Boundary //
        capComponent (T := T) b = D}), _root_.Set.range (K.cap b.1) := by
      rcases hn with hn | hn
      · obtain ⟨w, -, hwn⟩ := hn
        exact absurd ⟨w, hwn⟩ hcore
      · exact hn
    have hnuc' : n ∈ ⋃ (b : {b : T.Boundary //
        capComponent (T := T) b = D'}), _root_.Set.range (K.cap b.1) := by
      rcases hn' with hn' | hn'
      · obtain ⟨w, -, hwn⟩ := hn'
        exact absurd ⟨w, hwn⟩ hcore
      · exact hn'
    obtain ⟨⟨b, hb⟩, hbn⟩ := mem_iUnion.mp hnuc
    obtain ⟨⟨b', hb'⟩, hb'n⟩ := mem_iUnion.mp hnuc'
    have hbb' : b ≠ b' := by
      intro hEq
      exact hne (by rw [← hb, ← hb', hEq])
    exact Set.disjoint_left.mp (K.cap_disjoint hbb') hbn hb'n

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_pairwise_disjoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.piece_pairwise_disjoint target :: scope.openDecls } }

theorem rfs_cap_component_bijection [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N] : Function.Bijective K.componentMap := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have hab' : ConnectedComponents.mk (K.coreInclusion x) =
        ConnectedComponents.mk (K.coreInclusion y) := by
      simpa only [componentMap, Continuous.connectedComponentsMap_mk] using hab
    have hmem : K.coreInclusion y ∈ connectedComponent (K.coreInclusion x) :=
      ConnectedComponents.coe_eq_coe'.mp hab'.symm
    have hx : K.coreInclusion x ∈ piece K (ConnectedComponents.mk x) :=
      (coreInclusion_mem_piece_iff K).mpr rfl
    have hxmem : K.coreInclusion x ∈ connectedComponent (K.coreInclusion x) := mem_connectedComponent
    set v := ⋃ D' ∈ {D' : ConnectedComponents T.core | D' ≠ ConnectedComponents.mk x},
      piece K D' with hv
    have hvc : IsClosed v := by
      rw [hv]
      refine (Set.toFinite
        ({D' : ConnectedComponents T.core | D' ≠ ConnectedComponents.mk x})).isClosed_biUnion ?_
      intro D' _
      exact piece_isClosed K D'
    have hsub : connectedComponent (K.coreInclusion x) ⊆
        piece K (ConnectedComponents.mk x) ∪ v := by
      intro n _
      have hn' : n ∈ ⋃ D', piece K D' := by
        rw [piece_cover K]
        exact _root_.Set.mem_univ n
      obtain ⟨D', hD'⟩ := mem_iUnion.mp hn'
      by_cases hD : D' = ConnectedComponents.mk x
      · exact Or.inl (hD ▸ hD')
      · exact Or.inr (mem_iUnion.mpr ⟨D', mem_iUnion.mpr ⟨hD, hD'⟩⟩)
    have hdisj : connectedComponent (K.coreInclusion x) ∩
        (piece K (ConnectedComponents.mk x) ∩ v) = ∅ := by
      rw [_root_.Set.eq_empty_iff_forall_notMem]
      rintro n ⟨_, hnu, hnv⟩
      obtain ⟨D', hD'⟩ := mem_iUnion.mp hnv
      obtain ⟨hD'ne, hnD'⟩ := mem_iUnion.mp hD'
      exact Set.disjoint_left.mp (piece_pairwise_disjoint K hD'ne) hnD' hnu
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponent (x := K.coreInclusion x)))
      (piece K (ConnectedComponents.mk x)) v (piece_isClosed K _) hvc hsub hdisj with hCu | hCv
    · exact ((coreInclusion_mem_piece_iff K).mp (hCu hmem)).symm
    · exact absurd (hCv hxmem) (fun hxuv =>
        (Set.eq_empty_iff_forall_notMem.mp hdisj) (K.coreInclusion x) ⟨hxmem, hx, hxuv⟩)
  · intro c
    obtain ⟨n, rfl⟩ := ConnectedComponents.surjective_coe c
    have hn' : n ∈ ⋃ D, piece K D := by
      rw [piece_cover K]
      exact _root_.Set.mem_univ n
    obtain ⟨D, hD⟩ := mem_iUnion.mp hn'
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe D
    have hzn : n ∈ piece K (ConnectedComponents.mk z) := hD
    have hzc : K.coreInclusion z ∈ piece K (ConnectedComponents.mk z) :=
      (coreInclusion_mem_piece_iff K).mpr rfl
    have hsame : ConnectedComponents.mk n = ConnectedComponents.mk (K.coreInclusion z) :=
      ConnectedComponents.coe_eq_coe'.mpr
        (((piece_preconnected K (ConnectedComponents.mk z)).subset_connectedComponent
          hzc) hzn)
    exact ⟨ConnectedComponents.mk z, by
      simpa only [componentMap, Continuous.connectedComponentsMap_mk] using hsame.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection


def componentEquiv [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N] :
    ConnectedComponents T.core ≃ ConnectedComponents N :=
  Equiv.ofBijective K.componentMap K.rfs_cap_component_bijection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.componentEquiv


theorem component_meets_core [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N]
    (c : ConnectedComponents N) :
    ∃ x : T.core, ConnectedComponents.mk (K.coreInclusion x) = c := by
  obtain ⟨d, hd⟩ := K.rfs_cap_component_bijection.surjective c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  exact ⟨x, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.component_meets_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.component_meets_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.component_meets_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.component_meets_core

end Capping

structure CutCapTopology (M Q D N : Type*) [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N] where
  tubes : TubeSystem M
  capping : Capping tubes N
  presentation : N ≃ₜ Q ⊕ D
  nontrivial : Nonempty tubes.Index ∨ Nonempty D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)


def retainedCore : Set E.tubes.core :=
  {x | ∃ q : Q, E.presentation (E.capping.coreInclusion x) = Sum.inl q}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore


def cappedChild (c : ConnectedComponents Q) : ConnectedComponents N :=
  (E.presentation.symm.continuous.comp continuous_inl).connectedComponentsMap c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.cappedChild then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.cappedChild"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.cappedChild ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.cappedChild


def childCore [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] [T2Space N]
    (c : ConnectedComponents Q) : ConnectedComponents E.tubes.core :=
  E.capping.componentEquiv.symm (E.cappedChild c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore


def rfs_child_parent [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] [T2Space N]
    (c : ConnectedComponents Q) : ConnectedComponents M :=
  continuous_subtype_val.connectedComponentsMap (E.childCore c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.rfs_child_parent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.rfs_child_parent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.rfs_child_parent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.rfs_child_parent


theorem childCore_unique [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core]
    [T2Space N] (c : ConnectedComponents Q) :
    ∃! d : ConnectedComponents E.tubes.core,
      E.capping.componentMap d = E.cappedChild c := by
  exact E.capping.rfs_cap_component_bijection.existsUnique _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_unique

theorem childCore_subset_retainedCore [CompactSpace E.tubes.core]
    [LocallyConnectedSpace E.tubes.core] [T2Space N]
    (c : ConnectedComponents Q) {z : E.tubes.core}
    (hz : ConnectedComponents.mk z = E.childCore c) : z ∈ E.retainedCore := by
  classical
  obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe c
  have hcore : E.capping.componentMap (E.childCore c) = E.cappedChild c :=
    E.capping.componentEquiv.apply_symm_apply _
  have hx : ConnectedComponents.mk (E.capping.coreInclusion z) = E.cappedChild c := by
    rw [← hcore, ← hz]
    rfl
  have hpres : ConnectedComponents.mk (E.presentation (E.capping.coreInclusion z)) =
      ConnectedComponents.mk (Sum.inl q : Q ⊕ D) := by
    have h := congrArg E.presentation.continuous.connectedComponentsMap hx
    simpa [CutCapTopology.cappedChild, ← hq] using h
  have hmem : E.presentation (E.capping.coreInclusion z) ∈
      connectedComponent (Sum.inl q : Q ⊕ D) :=
    ConnectedComponents.coe_eq_coe'.mp hpres
  have hrange : E.presentation (E.capping.coreInclusion z) ∈ Set.range (Sum.inl : Q → Q ⊕ D) :=
    isClopen_range_inl.connectedComponent_subset (Set.mem_range_self q) hmem
  obtain ⟨q', hq'⟩ := hrange
  exact ⟨q', hq'.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_subset_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_subset_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_subset_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.childCore_subset_retainedCore
end CutCapTopology

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
