import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeBoundaryComponents
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCoreBoundaryOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapDecomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball target :: scope.openDecls } }
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
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IH target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
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

private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def FiniteCutCapGeometry (hδ1 : ∀ i, precision i < 1)
    (R : Set (ConnectedComponents (cutCore f))) : Prop :=
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
    let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
    let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
    let c := fun (b : ι × Bool) (x : Ball L) => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩
    let F := (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm
    let jRet := finiteRetainedCoreInclusion hL hδ f hf hdisj R
    let jDisc := finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ
    (Nonempty M) ∧
    (∀ i, _root_.Manifold.IsSmoothEmbedding IR I ∞ (ν i)) ∧
    (Pairwise (fun i k => Disjoint (_root_.Set.range (ν i)) (_root_.Set.range (ν k)))) ∧
    (cutCore f = (⋃ i, ν i '' {q : S2 × _root_.Set.Icc (-2 : ℝ) 2 | q.2.val ∈ _root_.Set.Ioo (-1 : ℝ) 1})ᶜ) ∧
    (IsCompact (cutCore f)) ∧
    (IsCompact (retainedCore f R) ∧ IsCompact (retainedCore f Rᶜ)) ∧
    (_root_.Manifold.IsSmoothEmbedding IR I ∞ (Subtype.val : cutCore f → M)) ∧
    (_root_.Manifold.IsSmoothEmbedding IR I ∞ (fun p : retainedCore f R => p.val.val)) ∧
    (_root_.Manifold.IsSmoothEmbedding IR I ∞ (fun p : retainedCore f Rᶜ => p.val.val)) ∧
    (CompactSpace Q ∧ T2Space Q ∧ SecondCountableTopology Q) ∧
    (IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧ IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) ∧ CompactSpace (finiteCapRetained hL hδ f hf hdisj R) ∧ CompactSpace (finiteCapDiscarded hL hδ f hf hdisj R) ∧ T2Space (finiteCapRetained hL hδ f hf hdisj R) ∧ T2Space (finiteCapDiscarded hL hδ f hf hdisj R) ∧ SecondCountableTopology (finiteCapRetained hL hδ f hf hdisj R) ∧ SecondCountableTopology (finiteCapDiscarded hL hδ f hf hdisj R)) ∧
    ((𝓡 3).boundary Q = ∅ ∧ (𝓡 3).boundary (finiteCapRetained hL hδ f hf hdisj R) = ∅ ∧ (𝓡 3).boundary (finiteCapDiscarded hL hδ f hf hdisj R) = ∅) ∧
    (∀ (b : ι × Bool) (y : S2), nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs b = ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y)) ∧
    (∀ (b : ι × Bool) (y : S2), connectedComponent (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) = _root_.Set.range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) ∧
    (_root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞ j) ∧
    (∀ b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (c b)) ∧
    (_root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞ jRet) ∧
    (_root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞ jDisc) ∧
    (_root_.Set.range j ∪ (⋃ b, _root_.Set.range (c b)) = _root_.Set.univ) ∧
    (∀ b, _root_.Set.range j ∩ _root_.Set.range (c b) = _root_.Set.range (fun p : nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b => j p.val.val)) ∧
    (∀ b, _root_.Set.range (fun p : nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b => j p.val.val) = _root_.Set.range (fun x : BoundaryManifold (𝓡∂ 3) (Ball L) => c b x.val)) ∧
    (Pairwise (fun b k => Disjoint (_root_.Set.range (c b)) (_root_.Set.range (c k)))) ∧
    (∀ (b : ι × Bool) (x : BoundaryManifold (𝓡∂ 3) (Ball L)), c b x.val = j (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val) ∧
    (∀ p : retainedCore f R, F (j p.val) = Sum.inl (jRet p)) ∧
    (∀ p : retainedCore f Rᶜ, F (j p.val) = Sum.inr (jDisc p)) ∧
    (retainedCore f R = (F ∘ j) ⁻¹' _root_.Set.range Sum.inl) ∧
    (∀ q : finiteCapRetained hL hδ f hf hdisj R, ∃ p : retainedCore f R, jRet p ∈ connectedComponent q) ∧
    ((interior (_root_.Set.range jRet))ᶜ = ⋃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, _root_.Set.range (fun x : Ball L => (⟨c b.val x, b.property⟩ : finiteCapRetained hL hδ f hf hdisj R))) ∧
    (Nonempty (finiteCapRetained hL hδ f hf hdisj R) ↔ Nonempty (retainedCore f R)) ∧
    (Nonempty ι ∨ Nonempty (finiteCapDiscarded hL hδ f hf hdisj R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCutCapGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCutCapGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCutCapGeometry ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCutCapGeometry

theorem finiteCutCapGeometry [CompactSpace M] [Nonempty M]
    (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f)))
    (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)) :
    FiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
  let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let c := fun (b : ι × Bool) (x : Ball L) => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩
  let F := (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm
  let jRet := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let jDisc := finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ
  have htop := finiteCapQuotient_topological_properties I hdim hL hδ f hf hdisj
  refine ⟨inferInstance,
    fun i => originalTubularMap_isSmoothEmbedding I hdim (hδ i) (hδ1 i) (f i) (hf i) (hs i),
    originalTubularMap_pairwise_disjoint hδ hδ1 f hdisj,
    cutCore_eq_originalTubularComplement hδ hδ1 f,
    isCompact_cutCore f hf,
    isCompact_retained_discardedCore hδ f hf hdisj R,
    cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj Rᶜ hs,
    ⟨htop.1, htop.2.1, htop.2.2.1⟩,
    finiteCapSelected_closedManifold_properties I hdim hL hδ f hf hdisj hs R,
    ⟨ModelWithCorners.Boundaryless.boundary_eq_empty, ModelWithCorners.Boundaryless.boundary_eq_empty, ModelWithCorners.Boundaryless.boundary_eq_empty⟩,
    nativeCuttingSphereComponentsEquiv_apply I hdim hδ f hf hdisj hs,
    nativeCuttingSphereMap_connectedComponent I hdim hδ f hf hdisj hs,
    finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs,
    finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs,
    finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R,
    finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs Rᶜ,
    ?cover,
    ?inter,
    ?native,
    finiteCap_ball_images_disjoint hL hδ f hf hdisj,
    nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL,
    ?ret,
    ?disc,
    ?preimage,
    finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R,
    finiteRetained_compl_interior_core hL hδ f hf hdisj R,
    finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj R,
    hnontrivial.imp_right ((finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj Rᶜ).mpr)⟩
  case cover =>
    ext q
    constructor
    · exact fun _ => _root_.Set.mem_univ q
    · intro _
      have h := Set.ext_iff.mp (finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj) q
      rcases h.mpr (_root_.Set.mem_univ q) with ⟨⟨b, x⟩, hx⟩ | hj
      · exact Or.inr (mem_iUnion.mpr ⟨b, ⟨x, hx⟩⟩)
      · exact Or.inl hj
  case inter =>
    intro b
    apply (finiteCap_core_inter_ball hL hδ f hf hdisj b).trans
    let D := nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨D y, congrArg j (nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b y)⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨y, rfl⟩ := D.surjective p
      exact ⟨y, (congrArg j (nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b y)).symm⟩
  case native =>
    intro b
    let φ := nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := φ.surjective p
      exact ⟨x, nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL b x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨φ x, (nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL b x).symm⟩
  case ret =>
    intro p
    exact finiteCapSelectedDiffeomorph_symm_retained I hdim hL hδ f hf hdisj R (j p.val) p.property
  case disc =>
    intro p
    exact finiteCapSelectedDiffeomorph_symm_discarded I hdim hL hδ f hf hdisj R (j p.val) p.property
  case preimage =>
    ext p
    constructor
    · intro hp
      exact ⟨jRet ⟨p, hp⟩, (finiteCapSelectedDiffeomorph_symm_retained I hdim hL hδ f hf hdisj R (j p) hp).symm⟩
    · rintro ⟨q, hq⟩
      have hv := congrArg F.symm hq
      change q.val = F.symm (F (j p)) at hv
      rw [F.symm_apply_apply] at hv
      have hr := q.property
      change q.val ∈ (finiteCapRetained hL hδ f hf hdisj R : Set Q) at hr
      rw [hv] at hr
      exact hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCutCapGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCutCapGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCutCapGeometry ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCutCapGeometry
end DifferentialGeometry.Topology.ThreeManifold.Surgery
