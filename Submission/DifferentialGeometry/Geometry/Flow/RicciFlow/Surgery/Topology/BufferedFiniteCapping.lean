import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedTubeSystem
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import Submission.DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

omit [T2Space M] in
def bufferedCutCoreHomeomorph : (T).core ≃ₜ cutCore f :=
  Homeomorph.setCongr (TubeSystem.ofBufferedCharts_core hδ hδ1 f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph

omit [T2Space M] in
theorem bufferedCutCoreHomeomorph_boundary (b : ι × Bool) (y : Sphere 2) :
    bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj ((T).coreBoundarySphere b y) =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ := by
  apply Subtype.ext
  rcases b with ⟨i, side⟩
  cases side <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedCutCoreHomeomorph_boundary

private def scaledThreeBallHomeomorph : ThreeBall ≃ₜ {x : ThreeSpace // ‖x‖ ≤ L} :=
  (DifferentialGeometry.Topology.Handle.closedCellBallHomeo 3).symm.trans (closedBallUnitHomeomorph hL).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaledThreeBallHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaledThreeBallHomeomorph target :: scope.openDecls } }

private theorem scaledThreeBallHomeomorph_boundary (y : Sphere 2) :
    scaledThreeBallHomeomorph hL (sphereToThreeBall y) =
      DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary hL y := by
  apply Subtype.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaledThreeBallHomeomorph_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaledThreeBallHomeomorph_boundary target :: scope.openDecls } }

private def bufferedFiniteCoreMap : C((T).core, Q) :=
  ⟨fun x => finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x),
    (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).continuous.comp
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).continuous⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedFiniteCoreMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedFiniteCoreMap target :: scope.openDecls } }

private def bufferedFiniteCapMap (b : ι × Bool) : C(ThreeBall, Q) :=
  ⟨fun x => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
      ⟨b, scaledThreeBallHomeomorph hL x⟩,
    (isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).continuous.comp
      (continuous_sigmaMk.comp (scaledThreeBallHomeomorph hL).continuous)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedFiniteCapMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedFiniteCapMap target :: scope.openDecls } }

private theorem range_bufferedFiniteCoreMap :
    _root_.Set.range (bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj) =
      range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) :=
  (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).surjective.range_comp
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_bufferedFiniteCoreMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_bufferedFiniteCoreMap target :: scope.openDecls } }

private theorem range_bufferedFiniteCapMap (b : ι × Bool) :
    _root_.Set.range (bufferedFiniteCapMap hL hδ f hf hdisj b) =
      _root_.Set.range (fun x : {x : ThreeSpace // ‖x‖ ≤ L} =>
        finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) :=
  (scaledThreeBallHomeomorph hL).surjective.range_comp
    (fun x => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_bufferedFiniteCapMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_bufferedFiniteCapMap target :: scope.openDecls } }

def Capping.ofBufferedFiniteCaps : Capping T Q where
  coreInclusion := bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj
  coreEmbedding := (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding.comp
    (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).isEmbedding
  cap := bufferedFiniteCapMap hL hδ f hf hdisj
  capEmbedding b :=
    (isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).isEmbedding.comp
      (_root_.Topology.IsEmbedding.sigmaMk.comp (scaledThreeBallHomeomorph hL).isEmbedding)
  attaching := fun _ => Homeomorph.refl _
  boundary_eq b y := by
    change ι × Bool at b
    change finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
        ⟨b, scaledThreeBallHomeomorph hL (sphereToThreeBall y)⟩ =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj ((T).coreBoundarySphere b y))
    rw [scaledThreeBallHomeomorph_boundary, bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y]
    exact finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  exhaustive := by
    change _root_.Set.range (bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj) ∪
      (⋃ b : ι × Bool, _root_.Set.range (bufferedFiniteCapMap hL hδ f hf hdisj b)) = _root_.Set.univ
    rw [range_bufferedFiniteCoreMap]
    simp_rw [range_bufferedFiniteCapMap]
    have h := finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj
    rw [_root_.Set.union_comm] at h
    convert h using 2
    ext q
    simp only [_root_.Set.mem_iUnion, _root_.Set.mem_range]
    constructor
    · rintro ⟨b, x, rfl⟩
      exact ⟨⟨b, x⟩, rfl⟩
    · rintro ⟨⟨b, x⟩, rfl⟩
      exact ⟨b, x, rfl⟩
  core_cap_intersection b := by
    rw [range_bufferedFiniteCoreMap hL hδ hδ1 f hf hdisj, range_bufferedFiniteCapMap hL hδ f hf hdisj b,
      finiteCap_core_inter_ball hL hδ f hf hdisj b]
    congr 1
    funext y
    exact congrArg (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y).symm
  cap_disjoint := by
    intro b c hbc
    change ι × Bool at b c
    rw [range_bufferedFiniteCapMap hL hδ f hf hdisj b, range_bufferedFiniteCapMap hL hδ f hf hdisj c]
    exact finiteCap_ball_images_disjoint hL hδ f hf hdisj hbc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps

theorem Capping.ofBufferedFiniteCaps_coreInclusion (x : (T).core) :
    (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion x =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_coreInclusion

theorem Capping.ofBufferedFiniteCaps_cap (b : ι × Bool) (x : ThreeBall) :
    (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).cap b x =
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
        ⟨b, ⟨L • (x : ThreeSpace), by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
          have hx : ‖(x : ThreeSpace)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
          nlinarith⟩⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.ofBufferedFiniteCaps_cap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
