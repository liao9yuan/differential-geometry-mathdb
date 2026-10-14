import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorToCollar

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
private abbrev CoreSmoothE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothE2 target :: scope.openDecls } }
private abbrev CoreSmoothIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIR target :: scope.openDecls } }
private abbrev CoreSmoothIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIC target :: scope.openDecls } }
private abbrev CoreSmoothIH := ModelProd CoreSmoothE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreSmoothIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem cutCore_isManifold
    (hs : ∀ i, IsLocalDiffeomorph CoreSmoothIC I ∞ (f i)) :
    let : ChartedSpace CoreSmoothIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsManifold CoreSmoothIR ∞ (cutCore f) := by
  let : ChartedSpace CoreSmoothIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  apply isManifold_of_contDiffOn CoreSmoothIR ∞ (cutCore f)
  intro e e' he he'
  have hT : ContMDiffOn CoreSmoothIR CoreSmoothIR ∞ (e.symm.trans e') (e.symm.trans e').source := by
    change e ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj at he
    change e' ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj at he'
    rcases he with ⟨p, rfl⟩ | ⟨⟨b, q⟩, rfl⟩
    · rcases he' with ⟨p', rfl⟩ | ⟨⟨b', q'⟩, rfl⟩
      · exact cutCoreInteriorHalfChart_contMDiff_transition I hdim f p p'
      · exact cutCoreInteriorHalfChart_to_collar_contMDiff I hdim hδ f hf hdisj hs b' q' p
    · rcases he' with ⟨p', rfl⟩ | ⟨⟨b', q'⟩, rfl⟩
      · exact cutCoreCollarHalfChart_to_interior_contMDiff I hdim hδ f hf hdisj (fun i => (hs i).contMDiff) b q p'
      · exact cutCoreCollarHalfChart_contMDiff_transition hδ f hf hdisj b b' q q'
  have hcoord := hT.comp
    (CoreSmoothIR.contMDiffOn_symm.mono
      (_root_.Set.inter_subset_right : CoreSmoothIR.symm ⁻¹' (e.symm.trans e').source ∩ _root_.Set.range CoreSmoothIR ⊆ _root_.Set.range CoreSmoothIR))
    (fun z hz => hz.1)
  exact (CoreSmoothIR.contMDiff.comp_contMDiffOn hcoord).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_isManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_isManifold
end DifferentialGeometry.Topology.ThreeManifold.Surgery
