import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapFullInsertion
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPatchSelection
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev FullWE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWE3 target :: scope.openDecls } }
private abbrev FullWIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWIC target :: scope.openDecls } }
private abbrev FullWAttachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWAttachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullWAttachment target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceFullWE3FullWAttachment {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : ChartedSpace FullWE3 (FullWAttachment hL hB) :=
  radialCapAttachmentChartedSpace hL hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceFullWE3FullWAttachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instChartedSpaceFullWE3FullWAttachment target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopFullWAttachment {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (FullWAttachment hL hB) :=
  radialCapAttachment_isManifold hL hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopFullWAttachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopFullWAttachment target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instT2SpaceFullWAttachment {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : T2Space (FullWAttachment hL hB) :=
  radialCapAttachment_t2Space hL hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instT2SpaceFullWAttachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instT2SpaceFullWAttachment target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullWIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c)
local notation "FullWQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "FullWRet" => finiteCapRetained hL hδ f hf hdisj R
local notation "FullWB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

def finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    FullWAttachment hL (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 → FullWRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) ∘
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap

theorem contMDiff_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_inclusion (n := ∞) (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹))).comp
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteFullWitnessMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteFullWitnessMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteFullWitnessMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteFullWitnessMap

theorem finiteFullWitnessMap_mfderiv (b : FullWB) (q : FullWAttachment hL (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) q =
      mfderiv (𝓡 3) (𝓡 3) (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  change mfderiv (𝓡 3) (𝓡 3) (Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) ∘ D.symm) q = _
  rw [mfderiv_comp q ((contMDiff_inclusion (n := ∞) (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹))).mdifferentiable (by simp) (D.symm q))
    (D.symm.contMDiff.mdifferentiable (by simp) q), mfderiv_opens_incl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteFullWitnessMap_mfderiv

theorem injective_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Injective (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  dsimp only
  intro x y he
  apply D.symm.injective
  apply Subtype.ext
  exact congrArg (fun q : FullWRet => q.val) he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteFullWitnessMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteFullWitnessMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteFullWitnessMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteFullWitnessMap

theorem isLocalDiffeomorph_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullWQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space FullWQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) _ rfl
  intro q
  rw [finiteFullWitnessMap_mfderiv]
  exact (D.symm.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) q).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteFullWitnessMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteFullWitnessMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteFullWitnessMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteFullWitnessMap

theorem range_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Set.range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) =
      {q : FullWRet | q.val ∈ finiteCapRestrictedNeighborhood hL hδ f hf hdisj b.val ((c * precision b.val.1)⁻¹)} := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (D.symm p).property
  · intro hq
    refine ⟨D ⟨q.val, hq⟩, ?_⟩
    change Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) (D.symm (D ⟨q.val, hq⟩)) = q
    rw [D.symm_apply_apply]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteFullWitnessMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteFullWitnessMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteFullWitnessMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteFullWitnessMap

theorem pairwise_disjoint_finiteFullWitnessMaps :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Pairwise (fun b d : FullWB => Disjoint
      (_root_.Set.range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b)) (_root_.Set.range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc d))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro b d hbd
  apply Set.disjoint_left.mpr
  intro q hb hd
  rw [range_finiteFullWitnessMap] at hb hd
  have hval : b.val ≠ d.val := fun he => hbd (Subtype.ext he)
  exact Set.disjoint_left.mp (pairwise_disjoint_finiteCapRestrictedNeighborhoods hL hδ f hf hdisj
    (fun b => (c * precision b.1)⁻¹) hval) hb hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteFullWitnessMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteFullWitnessMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteFullWitnessMaps ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteFullWitnessMaps
end DifferentialGeometry.Topology.ThreeManifold.Surgery
