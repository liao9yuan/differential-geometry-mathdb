import Submission.DifferentialGeometry.Geometry.Neck.RecenteringChart
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }

def centralDomain (δ : ℝ) : Set (bufferedCylinder δ) := {q | q.val.2 ∈ _root_.Set.Ioo (-1 : ℝ) 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.centralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.centralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.centralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.centralDomain

def closedCentralDomain (δ : ℝ) : Set (bufferedCylinder δ) := {q | q.val.2 ∈ _root_.Set.Icc (-1 : ℝ) 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.closedCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.closedCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.closedCentralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.closedCentralDomain

theorem isOpen_centralDomain (δ : ℝ) : IsOpen (centralDomain δ) :=
  isOpen_Ioo.preimage continuous_subtype_val.snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_centralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_centralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_centralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_centralDomain

theorem isCompact_closedCentralDomain (δ : ℝ) (hδ : 0 < δ) : IsCompact (closedCentralDomain δ) := by
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' closedCentralDomain δ = (_root_.Set.univ : Set S2) ×ˢ _root_.Set.Icc (-1 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_univ _, hq⟩
    · intro hp
      have hmem : p ∈ bufferedCylinder δ := by
        change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1
        constructor <;> linarith [inv_pos.mpr hδ, hp.2.1, hp.2.2]
      exact ⟨⟨p, hmem⟩, hp.2, rfl⟩
  rw [he]
  exact isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_closedCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_closedCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_closedCentralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_closedCentralDomain

theorem closure_centralDomain (δ : ℝ) : closure (centralDomain δ) = closedCentralDomain δ := by
  have hf : IsOpenMap (fun q : bufferedCylinder δ => q.val.2) :=
    isOpenMap_snd.comp (bufferedCylinder δ).isOpen.isOpenMap_subtype_val
  have he := hf.preimage_closure_eq_closure_preimage continuous_subtype_val.snd (_root_.Set.Ioo (-1 : ℝ) 1)
  simpa only [centralDomain, closedCentralDomain, Set.preimage, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_centralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_centralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_centralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_centralDomain

variable {M : Type*} [TopologicalSpace M] {δ : ℝ}

def removedSlab (f : bufferedCylinder δ → M) : Set M := f '' centralDomain δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab

def closedSlab (f : bufferedCylinder δ → M) : Set M := f '' closedCentralDomain δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.closedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.closedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.closedSlab ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.closedSlab

def cutFaces (hδ : 0 < δ) (f : bufferedCylinder δ → M) : Set M :=
  _root_.Set.range (fun y : S2 => f ⟨(y, -1), offset_mem_bufferedCylinder hδ (by norm_num) y⟩) ∪
    _root_.Set.range (fun y : S2 => f ⟨(y, 1), offset_mem_bufferedCylinder hδ (by norm_num) y⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutFaces ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutFaces

theorem isOpen_removedSlab (f : bufferedCylinder δ → M) (hf : _root_.Topology.IsOpenEmbedding f) :
    IsOpen (removedSlab f) := hf.isOpenMap _ (isOpen_centralDomain δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_removedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_removedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_removedSlab ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpen_removedSlab

theorem closure_removedSlab [T2Space M] (hδ : 0 < δ)
    (f : bufferedCylinder δ → M) (hf : Continuous f) : closure (removedSlab f) = closedSlab f := by
  have hc : IsCompact (closure (centralDomain δ)) := by
    rw [closure_centralDomain]
    exact isCompact_closedCentralDomain δ hδ
  have he := image_closure_of_isCompact hc hf.continuousOn
  simpa only [closure_centralDomain, removedSlab, closedSlab] using he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_removedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_removedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_removedSlab ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.closure_removedSlab

theorem frontier_removedSlab [T2Space M] (hδ : 0 < δ)
    (f : bufferedCylinder δ → M) (hf : _root_.Topology.IsOpenEmbedding f) :
    frontier (removedSlab f) = cutFaces hδ f := by
  rw [frontier, closure_removedSlab hδ f hf.continuous, (isOpen_removedSlab f hf).interior_eq]
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hn⟩
    have hnot : ¬(-1 < q.val.2 ∧ q.val.2 < 1) := fun hh => hn ⟨q, hh, rfl⟩
    have hends : q.val.2 = -1 ∨ q.val.2 = 1 := by
      change -1 ≤ q.val.2 ∧ q.val.2 ≤ 1 at hq
      rcases not_and_or.mp hnot with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hends with h | h
    · apply Or.inl
      refine ⟨q.val.1, congrArg f ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl h.symm
    · apply Or.inr
      refine ⟨q.val.1, congrArg f ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl h.symm
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨⟨_, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩
      rintro ⟨q, hq, he⟩
      have hp := congrArg (fun z : bufferedCylinder δ => z.val.2) (hf.injective he)
      change q.val.2 = -1 at hp
      have hh : -1 < q.val.2 := hq.1
      linarith
    · refine ⟨⟨_, ⟨by norm_num, le_rfl⟩, rfl⟩, ?_⟩
      rintro ⟨q, hq, he⟩
      have hp := congrArg (fun z : bufferedCylinder δ => z.val.2) (hf.injective he)
      change q.val.2 = 1 at hp
      have hh : q.val.2 < 1 := hq.2
      linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_removedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_removedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_removedSlab ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_removedSlab

variable {ι : Type*} {precision : ι → ℝ}

def cutCore (f : ∀ i : ι, bufferedCylinder (precision i) → M) : Set M :=
  (⋃ i, removedSlab (f i))ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore

theorem isClosed_cutCore (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) : IsClosed (cutCore f) :=
  (isOpen_iUnion (fun i => isOpen_removedSlab (f i) (hf i))).isClosed_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosed_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosed_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosed_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosed_cutCore

theorem isCompact_cutCore [CompactSpace M] (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) : IsCompact (cutCore f) :=
  (isClosed_cutCore f hf).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isCompact_cutCore

theorem frontier_cutCore [Finite ι] [T2Space M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    frontier (cutCore f) = ⋃ i, cutFaces (hδ i) (f i) := by
  have hopen := isOpen_iUnion (fun i => isOpen_removedSlab (f i) (hf i))
  rw [cutCore, frontier_compl, frontier, hopen.interior_eq, closure_iUnion_of_finite]
  simp_rw [closure_removedSlab (hδ _) _ (hf _).continuous]
  have hface (i : ι) : closedSlab (f i) \ removedSlab (f i) = cutFaces (hδ i) (f i) := by
    simpa only [frontier, closure_removedSlab (hδ i) _ (hf i).continuous,
      (isOpen_removedSlab (f i) (hf i)).interior_eq] using frontier_removedSlab (hδ i) (f i) (hf i)
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, hface i ▸ ⟨hi, fun hh => hn (mem_iUnion.mpr ⟨i, hh⟩)⟩⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hi' : p ∈ closedSlab (f i) \ removedSlab (f i) := hface i ▸ hi
    refine ⟨mem_iUnion.mpr ⟨i, hi'.1⟩, ?_⟩
    intro hn
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    by_cases hij : i = j
    · subst j
      exact hi'.2 hj
    · exact disjoint_left.mp (hdisj hij) (_root_.Set.image_subset_range _ _ hi'.1) (_root_.Set.image_subset_range _ _ hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.frontier_cutCore

section ActualNeckFamily
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def neckAmbientMap (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : bufferedCylinder δ → M := fun q => (d.map q : M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap

theorem isOpenEmbedding_neckAmbientMap (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : _root_.Topology.IsOpenEmbedding (neckAmbientMap U d) :=
  U.isOpen.isOpenEmbedding_subtypeVal.comp d.isOpenEmbedding_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_neckAmbientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_neckAmbientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_neckAmbientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_neckAmbientMap

theorem isLocalDiffeomorph_neckAmbientMap (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U}
    {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k) :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) I ∞ (neckAmbientMap U d) := by
  have hd : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) I ∞ d.map :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      d.map d.smooth d.immersion (by rw [show Module.finrank ℝ E = 3 from Fact.out]; simp)
  exact DifferentialGeometry.isLocalDiffeomorph_comp (DifferentialGeometry.isLocalDiffeomorph_subtype_val U) hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_neckAmbientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_neckAmbientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_neckAmbientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_neckAmbientMap

theorem range_neckAmbientMap_subset (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : _root_.Set.range (neckAmbientMap U d) ⊆ U := by
  rintro p ⟨q, rfl⟩
  exact (d.map q).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_neckAmbientMap_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_neckAmbientMap_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_neckAmbientMap_subset ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_neckAmbientMap_subset

theorem normalizedNeckFamily_cutCore [CompactSpace M] [Finite ι]
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (x₀ : ι → U) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (neckAmbientMap U (d i))) (_root_.Set.range (neckAmbientMap U (d j))))) :
    IsCompact (cutCore (fun i => neckAmbientMap U (d i))) ∧
      frontier (cutCore (fun i => neckAmbientMap U (d i))) =
        ⋃ i, cutFaces (d i).precision_pos (neckAmbientMap U (d i)) :=
  ⟨isCompact_cutCore _ (fun i => isOpenEmbedding_neckAmbientMap U (d i)),
    frontier_cutCore (fun i => (d i).precision_pos) _
      (fun i => isOpenEmbedding_neckAmbientMap U (d i)) hdisj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_cutCore
end ActualNeckFamily

omit [TopologicalSpace M] in
theorem cutCore_empty [IsEmpty ι] (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    cutCore f = univ := by simp [cutCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_empty ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_empty
end DifferentialGeometry.Topology.ThreeManifold.Surgery
