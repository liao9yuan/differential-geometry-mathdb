import Submission.DifferentialGeometry.Topology.Manifold.ProductBoundaryMap
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingCollarOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

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
private def sphereNativeCollar {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ BoundaryManifold IR (Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact (retainedFaceDiffeomorph hB).trans (retainedBoundaryFaceDiffeomorph hB).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereNativeCollar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereNativeCollar target :: scope.openDecls } }
private theorem sphereNativeCollar_apply {B : ℝ} (hB : 0 < B) (y : S2) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    (sphereNativeCollar hB y).val = (y, ⟨0, le_rfl, hB⟩) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact retainedBoundaryFaceDiffeomorph_symm_apply hB (retainedFaceDiffeomorph hB y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereNativeCollar_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereNativeCollar_apply target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

def nativeCuttingSphereMap (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    S2 → BoundaryManifold IR (cutCore f) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact productBoundaryMap (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) ∘ sphereNativeCollar hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap

theorem nativeCuttingSphereMap_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y).val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b,y⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  change cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b (sphereNativeCollar hB y).val = _
  rw [sphereNativeCollar_apply]
  exact cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_apply

theorem nativeCuttingSphereMap_contMDiff (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ContMDiff (𝓡 2) (𝓡 2) ∞ (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact (productBoundaryMap_contMDiff _ (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b)).comp
    (sphereNativeCollar hB).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_contMDiff

theorem nativeCuttingSphereMap_mfderiv_bijective (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Bijective (mfderiv (𝓡 2) (𝓡 2) (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let hκ := cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b
  exact bijective_mfderiv_comp (𝓡 2) (𝓡 2) (𝓡 2) (sphereNativeCollar hB) (productBoundaryMap κ hκ)
    (sphereNativeCollar hB).contMDiff (productBoundaryMap_contMDiff κ hκ)
    (fun x => ((sphereNativeCollar hB).mfderivToContinuousLinearEquiv (by simp) x).bijective)
    (productBoundaryMap_mfderiv_bijective κ hκ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_mfderiv_bijective

theorem nativeCuttingSphereMap_injective (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Injective (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro y z h
  have he := congrArg (fun p : BoundaryManifold IR (cutCore f) => p.val) h
  rw [nativeCuttingSphereMap_apply, nativeCuttingSphereMap_apply] at he
  have hp := (isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj).injective he
  exact congrArg (fun q : CuttingSpheres ι => q.2) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_injective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_injective

theorem nativeCuttingSphereMap_isLocalDiffeomorph (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact isLocalDiffeomorph_of_injective_mfderiv _ (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b)
    (fun y => (nativeCuttingSphereMap_mfderiv_bijective I hdim hδ f hf hdisj hs b y).injective) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isLocalDiffeomorph

theorem nativeCuttingSphereMap_isOpenEmbedding (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    _root_.Topology.IsOpenEmbedding (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact _root_.Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨(nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous,
      nativeCuttingSphereMap_injective I hdim hδ f hf hdisj hs b,
      (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).isOpenMap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_isOpenEmbedding

theorem nativeCuttingSphereMap_range_isClosed (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    IsClosed (_root_.Set.range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (isCompact_range (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_range_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_range_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_range_isClosed ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_range_isClosed

theorem nativeCuttingSphereMap_ranges_disjoint :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Pairwise (fun b c => Disjoint (_root_.Set.range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b))
      (_root_.Set.range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs c))) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro b c hbc
  rw [Set.disjoint_left]
  rintro p ⟨y, hy⟩ ⟨z, hz⟩
  have he := congrArg (fun q : BoundaryManifold IR (cutCore f) => q.val) (hy.trans hz.symm)
  rw [nativeCuttingSphereMap_apply, nativeCuttingSphereMap_apply] at he
  have hp := (isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj).injective he
  exact hbc (congrArg (fun q : CuttingSpheres ι => q.1) hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_ranges_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_ranges_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_ranges_disjoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_ranges_disjoint

theorem nativeCuttingSphereMap_cover :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ p : BoundaryManifold IR (cutCore f),
      ∃ (b : ι × Bool) (y : S2), nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y = p := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  have hp := (Set.ext_iff.mp (cutCore_boundary_eq_cuttingSpheres I hdim hδ f hf hdisj hs) p.val).mp p.property
  obtain ⟨⟨b, y⟩, hby⟩ := hp
  refine ⟨b, y, Subtype.ext ?_⟩
  exact (nativeCuttingSphereMap_apply I hdim hδ f hf hdisj hs b y).trans hby

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereMap_cover
end DifferentialGeometry.Topology.ThreeManifold.Surgery
