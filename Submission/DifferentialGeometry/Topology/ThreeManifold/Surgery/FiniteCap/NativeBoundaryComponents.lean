import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCuttingSpheres
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.SetTheory.Cardinal.Finite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Module _root_.Submission.Module _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E2 target :: scope.openDecls } }
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ER
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ER target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IH target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev Collar (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instHasSmoothBoundaryERIHIR : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instHasSmoothBoundaryERIHIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instHasSmoothBoundaryERIHIR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    ChartedSpace E2 (BoundaryManifold IR X) := BoundaryManifold.chartedSpace (I := IR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold IR X) := BoundaryManifold.isManifold (I := IR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

theorem nativeCuttingSphereMap_connectedComponent (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    connectedComponent (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) =
      range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  have hc := isConnected_range (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous
  have ho : IsClopen (_root_.Set.range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) :=
    ⟨nativeCuttingSphereMap_range_isClosed I hdim hδ f hf hdisj hs b, (nativeCuttingSphereMap_isOpenEmbedding I hdim hδ f hf hdisj hs b).isOpen_range⟩
  exact Subset.antisymm (ho.connectedComponent_subset ⟨y, rfl⟩) (hc.subset_connectedComponent ⟨y, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_connectedComponent ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_connectedComponent

def nativeCuttingSphereComponentsEquiv :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (ι × Bool) ≃ ConnectedComponents (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let β := nativeCuttingSphereMap I hdim hδ f hf hdisj hs
  apply Equiv.ofBijective (fun b : ι × Bool => ConnectedComponents.mk (β b spherePoint))
  constructor
  · intro b c he
    have hm : β b spherePoint ∈ connectedComponent (β c spherePoint) := ConnectedComponents.coe_eq_coe'.mp he
    have hc := nativeCuttingSphereMap_connectedComponent I hdim hδ f hf hdisj hs c spherePoint
    rw [hc] at hm
    by_contra hbc
    exact (Set.disjoint_left.mp (nativeCuttingSphereMap_ranges_disjoint I hdim hδ f hf hdisj hs hbc)) ⟨spherePoint, rfl⟩ hm
  · intro c
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨b, y, hp⟩ := nativeCuttingSphereMap_cover I hdim hδ f hf hdisj hs p
    refine ⟨b, ?_⟩
    apply ConnectedComponents.coe_eq_coe.mpr
    rw [← hp, nativeCuttingSphereMap_connectedComponent, nativeCuttingSphereMap_connectedComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv

theorem nativeCuttingSphereComponentsEquiv_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs b =
      ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  change ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b spherePoint) = _
  apply ConnectedComponents.coe_eq_coe.mpr
  rw [nativeCuttingSphereMap_connectedComponent, nativeCuttingSphereMap_connectedComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponentsEquiv_apply

theorem nativeCuttingSphereComponents_card :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Nat.card (ConnectedComponents (BoundaryManifold IR (cutCore f))) = 2 * Nat.card ι := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  have h := (Nat.card_congr (nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs)).symm
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponents_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponents_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponents_card ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereComponents_card
end DifferentialGeometry.Topology.ThreeManifold.Surgery
