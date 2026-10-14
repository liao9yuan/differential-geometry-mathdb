import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import Submission.DifferentialGeometry.Topology.Manifold.ScaledClosedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CapBallSmoothE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CapBallSmoothE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CapBallSmoothE3 target :: scope.openDecls } }
private abbrev CapBallSmoothIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CapBallSmoothIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CapBallSmoothIC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CapBallSmoothIC I ∞ (f i))
local notation "CapBallSmoothQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCapInclusion_ball_isSmoothEmbedding (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CapBallSmoothQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  let ρ : {x : CapBallSmoothE3 // ‖x‖ ≤ L} → V := fun x =>
    ⟨x.val, x.property.trans_lt (lt_add_of_pos_right L (cuttingCollarWidth_pos (hδ b.1)))⟩
  have hρ : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ρ :=
    isSmoothEmbedding_intoOpen (𝓡∂ 3) (𝓡 3) V ρ (isSmoothEmbedding_closedBall_inclusion hL)
  have hN : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (D.symm ∘ ρ) :=
    isSmoothEmbedding_diffeomorph_comp (𝓡∂ 3) (𝓡 3) ρ hρ D.symm
  have hQ : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val ∘ (D.symm ∘ ρ)) :=
    isSmoothEmbedding_fromOpen (𝓡∂ 3) (𝓡 3) N (D.symm ∘ ρ) hN
  have he : Subtype.val ∘ (D.symm ∘ ρ) =
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
    funext x
    let p : N := ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩
    have hp : D p = ρ x := Subtype.ext (finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b x)
    change (D.symm (ρ x)).val = p.val
    rw [← hp, D.symm_apply_apply]
  exact he ▸ hQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_isSmoothEmbedding

include hs in
theorem finiteRetainedCapInclusion_isSmoothEmbedding
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} =>
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩ : finiteCapRetained hL hδ f hf hdisj R)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CapBallSmoothQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact isSmoothEmbedding_intoOpen (𝓡∂ 3) (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R) _
    (finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCapInclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCapInclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCapInclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCapInclusion_isSmoothEmbedding

include hs in
theorem finiteDiscardedCapInclusion_isSmoothEmbedding
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∉ R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} =>
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩ : finiteCapDiscarded hL hδ f hf hdisj R)) :=
  finiteRetainedCapInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs Rᶜ b hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteDiscardedCapInclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteDiscardedCapInclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteDiscardedCapInclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteDiscardedCapInclusion_isSmoothEmbedding
end DifferentialGeometry.Topology.ThreeManifold.Surgery
