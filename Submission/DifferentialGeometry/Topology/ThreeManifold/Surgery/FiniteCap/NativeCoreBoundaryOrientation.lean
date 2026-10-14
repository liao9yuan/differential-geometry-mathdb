import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCuttingSpheres
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Module _root_.Submission.Module _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
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
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) := show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.isManifold (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }

private def pushThroughDiffeo {X Y : Type*} [TopologicalSpace X] [ChartedSpace E2 X] [IsManifold (𝓡 2) ∞ X]
    [TopologicalSpace Y] [ChartedSpace E2 Y] [IsManifold (𝓡 2) ∞ Y]
    (D : X ≃ₘ⟮𝓡 2, 𝓡 2⟯ Y) (o : SmoothOrientation (𝓡 2) X) : SmoothOrientation (𝓡 2) Y :=
  pullbackSmoothOrientation (𝓡 2) (𝓡 2) D.symm D.symm.contMDiff
    (fun p => (D.symm.mfderivToContinuousLinearEquiv (by simp) p).bijective) o

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pushThroughDiffeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.pushThroughDiffeo target :: scope.openDecls } }
private theorem pushThroughDiffeo_apply {X Y : Type*} [TopologicalSpace X] [ChartedSpace E2 X] [IsManifold (𝓡 2) ∞ X]
    [TopologicalSpace Y] [ChartedSpace E2 Y] [IsManifold (𝓡 2) ∞ Y]
    (D : X ≃ₘ⟮𝓡 2, 𝓡 2⟯ Y) (o : SmoothOrientation (𝓡 2) X) (y : X) :
    (pushThroughDiffeo D o).val (D y) =
      tangentOrientationEquiv (D.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv (o.val y) := by
  let A : E2 ≃L[ℝ] E2 := D.mfderivToContinuousLinearEquiv (by simp) y
  let hb := fun p => (D.symm.mfderivToContinuousLinearEquiv (by simp) p).bijective
  let B : E2 ≃L[ℝ] E2 := differentialEquivOfBijective (𝓡 2) (𝓡 2) D.symm hb (D y)
  have he : B = A.symm := by
    have hd := mfderiv_comp y (D.symm.contMDiff.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))
    have hid : D.symm ∘ D = id := funext D.symm_apply_apply
    rw [hid, mfderiv_id] at hd
    apply ContinuousLinearEquiv.ext
    funext v
    have hv := congrArg (fun T : E2 →L[ℝ] E2 => T (A.symm v)) hd
    change A.symm v = B (A (A.symm v)) at hv
    rw [A.apply_symm_apply] at hv
    exact hv.symm
  change tangentOrientationEquiv B.symm.toLinearEquiv (o.val (D.symm (D y))) =
    tangentOrientationEquiv A.toLinearEquiv (o.val y)
  rw [D.symm_apply_apply, he]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pushThroughDiffeo_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.pushThroughDiffeo_apply target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

def nativeCuttingSphereOpens (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Opens (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereOpens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereOpens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereOpens ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereOpens

def nativeCuttingSphereDiffeomorph (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact diffeomorphOntoImage (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)
    (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) (nativeCuttingSphereMap_injective I hdim hδ f hf hdisj hs b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph

theorem nativeCuttingSphereDiffeomorph_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y).val.val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact nativeCuttingSphereMap_apply I hdim hδ f hf hdisj hs b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCuttingSphereDiffeomorph_apply

private theorem sphereOpens_cover :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ p : BoundaryManifold IR (cutCore f), ∃ b, p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  obtain ⟨b, y, h⟩ := nativeCuttingSphereMap_cover I hdim hδ f hf hdisj hs p
  exact ⟨b, y, h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereOpens_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereOpens_cover target :: scope.openDecls } }

variable {L : ℝ} (hL : 0 < L) (oE : (ι × Bool) → Orientation ℝ E3 (Fin 3))
private def sphereComponentOrientation (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pushThroughDiffeo (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)
    (negSmoothOrientation (𝓡 2) (radialSphereSmoothOrientation hL (oE b)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereComponentOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereComponentOrientation target :: scope.openDecls } }
private theorem sphereComponentOrientation_compatible :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ (b c : ι × Bool) (p : BoundaryManifold IR (cutCore f))
      (hb : p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b) (hc : p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs c),
      (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE b).val ⟨p, hb⟩ =
        (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE c).val ⟨p, hc⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro b c p hb hc
  by_cases h : b = c
  · subst c
    rfl
  · exact ((Set.disjoint_left.mp (nativeCuttingSphereMap_ranges_disjoint I hdim hδ f hf hdisj hs h)) hb hc).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereComponentOrientation_compatible
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.sphereComponentOrientation_compatible target :: scope.openDecls } }

def nativeCoreBoundarySmoothOrientation :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation (𝓡 2) (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact glueSmoothOrientations (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE) (sphereOpens_cover I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation_compatible I hdim hδ f hf hdisj hs hL oE)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation

theorem nativeCoreBoundarySmoothOrientation_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val
      (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y).val =
        tangentOrientationEquiv ((nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b).mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
          (-(radialSphereSmoothOrientation hL (oE b)).val y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (glueSmoothOrientations_apply (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE) (sphereOpens_cover I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation_compatible I hdim hδ f hf hdisj hs hL oE) b (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y)).trans
      (pushThroughDiffeo_apply (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)
        (negSmoothOrientation (𝓡 2) (radialSphereSmoothOrientation hL (oE b))) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundarySmoothOrientation_apply

def nativeCoreBoundaryAttachingDiffeomorph (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    BoundaryManifold (𝓡∂ 3) (Ball L) ≃ₘ⟮𝓡 2, 𝓡 2⟯ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (closedBallBoundaryDiffeomorph hL).trans (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph

theorem nativeCoreBoundaryAttachingDiffeomorph_apply (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val =
        cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj
          ⟨b, closedBallBoundaryDiffeomorph hL x⟩ := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  exact nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b (closedBallBoundaryDiffeomorph hL x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_apply

theorem nativeCoreBoundaryAttachingDiffeomorph_coherence (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x.val⟩ =
        finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  have hx : radialCapBoundary hL (closedBallBoundaryDiffeomorph hL x) = x.val := by
    apply Subtype.ext
    change L • (L⁻¹ • x.val.val) = x.val.val
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  rw [nativeCoreBoundaryAttachingDiffeomorph_apply]
  have h := finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj
    ⟨b, closedBallBoundaryDiffeomorph hL x⟩
  change finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
    ⟨b, radialCapBoundary hL (closedBallBoundaryDiffeomorph hL x)⟩ = _ at h
  rw [hx] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_coherence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_coherence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_coherence ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_coherence

theorem nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      tangentOrientationEquiv ((nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        ((closedBallBoundarySmoothOrientation hL (oE b)).val x) =
          -(nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val
            (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  let d := closedBallBoundaryDiffeomorph hL
  let β := nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b
  let φ := nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b
  let A : E2 ≃L[ℝ] E2 := d.mfderivToContinuousLinearEquiv (by simp) x
  let B : E2 ≃L[ℝ] E2 := β.mfderivToContinuousLinearEquiv (by simp) (d x)
  let C : E2 ≃L[ℝ] E2 := φ.mfderivToContinuousLinearEquiv (by simp) x
  have he : C = A.trans B := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun D : E2 →L[ℝ] E2 => D v)
      (mfderiv_comp x (β.contMDiff.mdifferentiableAt (by simp)) (d.contMDiff.mdifferentiableAt (by simp)))
  let oB := (closedBallBoundarySmoothOrientation hL (oE b)).val x
  let oS := (radialSphereSmoothOrientation hL (oE b)).val (d x)
  have hA : tangentOrientationEquiv A.toLinearEquiv oB = oS :=
    closedBallBoundarySmoothOrientation_normalization hL (oE b) x
  have hN : (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (φ x).val =
      tangentOrientationEquiv B.toLinearEquiv (-oS) :=
    nativeCoreBoundarySmoothOrientation_apply I hdim hδ f hf hdisj hs hL oE b (d x)
  change tangentOrientationEquiv C.toLinearEquiv oB = _
  calc
    tangentOrientationEquiv C.toLinearEquiv oB =
        tangentOrientationEquiv B.toLinearEquiv (tangentOrientationEquiv A.toLinearEquiv oB) := by
      rw [he]
      exact tangentOrientationEquiv_trans A.toLinearEquiv B.toLinearEquiv oB
    _ = tangentOrientationEquiv B.toLinearEquiv oS := congrArg (tangentOrientationEquiv B.toLinearEquiv) hA
    _ = -(nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (φ x).val := by
      have hn := congrArg (fun q : Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) => -q) hN
      have hm := congrArg (fun q : Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) => -q)
        (tangentOrientationEquiv_neg B.toLinearEquiv oS)
      exact (hn.trans (hm.trans (neg_neg (tangentOrientationEquiv B.toLinearEquiv oS)))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation
end DifferentialGeometry.Topology.ThreeManifold.Surgery
