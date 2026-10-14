import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreCollarImmersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev EmbeddedE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedE2 target :: scope.openDecls } }
private abbrev EmbeddedIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIR target :: scope.openDecls } }
private abbrev EmbeddedIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIC target :: scope.openDecls } }
private abbrev EmbeddedIH := ModelProd EmbeddedE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.EmbeddedIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph EmbeddedIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_isSmoothEmbedding :
    let : ChartedSpace EmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsSmoothEmbedding EmbeddedIR I ∞ (Subtype.val : cutCore f → M) := by
  let : ChartedSpace EmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  refine ⟨?_, _root_.Topology.IsEmbedding.subtypeVal⟩
  suffices h : _root_.Manifold.IsImmersionOfComplement Unit EmbeddedIR I ∞ (Subtype.val : cutCore f → M) from h.isImmersion
  intro p
  by_cases hp : p.val ∈ interior (cutCore f)
  · exact cutCore_ambientInclusion_isImmersionAt_interior I hdim hδ f hf hdisj hs ⟨p.val, hp⟩
  · have hfront : p ∈ _root_.Set.range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    let q : _ × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    have hq : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q = p :=
      (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
    have h : _root_.Manifold.IsImmersionAtOfComplement Unit EmbeddedIR I ∞ (Subtype.val : cutCore f → M)
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) :=
      cutCore_ambientInclusion_isImmersionAt_collar I hdim hδ f hf hdisj hs b q
    exact hq ▸ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isSmoothEmbedding
end DifferentialGeometry.Topology.ThreeManifold.Surgery
