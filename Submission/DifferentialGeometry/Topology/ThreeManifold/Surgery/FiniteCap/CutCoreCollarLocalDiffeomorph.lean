import Submission.DifferentialGeometry.Topology.Manifold.LiftedChartLocalDiffeomorph
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
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev LocalCollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarE3 target :: scope.openDecls } }
private abbrev LocalCollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarE2 target :: scope.openDecls } }
private abbrev LocalCollarS2 := Metric.sphere (0 : LocalCollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarS2 target :: scope.openDecls } }
private abbrev LocalCollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIR target :: scope.openDecls } }
private abbrev LocalCollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIC target :: scope.openDecls } }
private abbrev LocalCollarIH := ModelProd LocalCollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.LocalCollarIH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealLocalCollarE3HAddOfNat : Fact (Module.finrank ℝ LocalCollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealLocalCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealLocalCollarE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph LocalCollarIC I ∞ (f i))

include hs in
theorem cuttingCollarMap_isLocalDiffeomorph (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace LocalCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsLocalDiffeomorph LocalCollarIR LocalCollarIR ∞
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace LocalCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold LocalCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  apply isLocalDiffeomorph_of_lifted_charts LocalCollarIR _ (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)
  intro q
  apply _root_.IsManifold.subset_maximalAtlas
  exact Or.inr ⟨⟨b, q⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_isLocalDiffeomorph
end DifferentialGeometry.Topology.ThreeManifold.Surgery
