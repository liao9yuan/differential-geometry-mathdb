import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.IsManifold
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev AmbientE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientE2 target :: scope.openDecls } }
private abbrev AmbientIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIR target :: scope.openDecls } }
private abbrev AmbientIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIC target :: scope.openDecls } }
private abbrev AmbientIH := ModelProd AmbientE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.AmbientIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph AmbientIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_contMDiff :
    let : ChartedSpace AmbientIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    ContMDiff AmbientIR I ∞ (Subtype.val : cutCore f → M) := by
  let : ChartedSpace AmbientIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold AmbientIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  obtain ⟨e, he, hp⟩ := cutCoreBoundaryAtlas_covers I hdim hδ f hf hdisj p
  have ha : e ∈ _root_.IsManifold.maximalAtlas AmbientIR ∞ (cutCore f) :=
    _root_.IsManifold.subset_maximalAtlas he
  have hR : ContMDiffOn AmbientIR I ∞ (fun z : AmbientIH => (e.symm z).val) e.target := by
    rcases he with ⟨x, rfl⟩ | ⟨⟨b, q⟩, rfl⟩
    · exact cutCoreInteriorHalfChart_symm_ambient_contMDiffOn I hdim f x
    · exact cutCoreCollarHalfChart_symm_ambient_contMDiffOn I hδ f hdisj
        (fun i => (hs i).contMDiff) hf b q
  have hc : ContMDiffAt AmbientIR AmbientIR ∞ e p := contMDiffAt_of_mem_maximalAtlas ha hp
  have hcomp := (hR.contMDiffAt (e.open_target.mem_nhds (e.map_source hp))).comp p hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (congrArg Subtype.val (e.left_inv hq)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_contMDiff
end DifferentialGeometry.Topology.ThreeManifold.Surgery
