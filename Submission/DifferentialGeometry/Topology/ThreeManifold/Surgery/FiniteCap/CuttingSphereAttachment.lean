import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SphericalCutCore

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck
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

def cuttingSign (b : Bool) : ℝ := if b then 1 else -1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign

theorem cuttingSign_sq (b : Bool) : cuttingSign b ^ 2 = 1 := by cases b <;> norm_num [cuttingSign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign_sq ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSign_sq

abbrev CuttingSpheres (ι : Type*) := Σ _b : ι × Bool, S2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.CuttingSpheres then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.CuttingSpheres"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.CuttingSpheres ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CuttingSpheres

variable {ι M : Type*} {precision : ι → ℝ}

def cuttingSphereMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) : CuttingSpheres ι → M :=
  fun p => f p.1.1 ⟨(p.2, cuttingSign p.1.2),
    offset_mem_bufferedCylinder (hδ p.1.1) (cuttingSign_sq p.1.2) p.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap

theorem range_cuttingSphereMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    range (cuttingSphereMap hδ f) = ⋃ i, cutFaces (hδ i) (f i) := by
  ext x
  constructor
  · rintro ⟨⟨⟨i, b⟩, y⟩, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    cases b
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hi with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨⟨(i, _root_.Bool.false), y⟩, hy⟩
    · exact ⟨⟨(i, _root_.Bool.true), y⟩, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereMap

theorem injective_cuttingSphereMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    Injective (cuttingSphereMap hδ f) := by
  rintro ⟨⟨i, b⟩, y⟩ ⟨⟨j, c⟩, z⟩ he
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (hdisj hne) ⟨_, rfl⟩ ⟨_, he.symm⟩
  subst j
  have hp := hf i he
  have hy : y = z := congrArg (fun q : bufferedCylinder (precision i) => q.val.1) hp
  have hs : cuttingSign b = cuttingSign c := congrArg (fun q : bufferedCylinder (precision i) => q.val.2) hp
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · have hh : (-1 : ℝ) = 1 := hs
      norm_num at hh
    · have hh : (1 : ℝ) = -1 := hs
      norm_num at hh
    · rfl
  subst c
  subst z
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_cuttingSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_cuttingSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_cuttingSphereMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_cuttingSphereMap

theorem cuttingSphereMap_mem_cutCore (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) (p : CuttingSpheres ι) :
    cuttingSphereMap hδ f p ∈ cutCore f := by
  rintro hn
  obtain ⟨j, q, hq, he⟩ := mem_iUnion.mp hn
  by_cases hij : p.1.1 = j
  · subst j
    have hp := hf p.1.1 he
    have hs := congrArg (fun q : bufferedCylinder (precision p.1.1) => q.val.2) hp
    change q.val.2 = cuttingSign p.1.2 at hs
    have hh : -1 < q.val.2 ∧ q.val.2 < 1 := hq
    cases h : p.1.2 <;> simp [h, cuttingSign] at hs <;> linarith [hh.1, hh.2]
  · exact disjoint_left.mp (hdisj hij) ⟨_, rfl⟩ ⟨q, he⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap_mem_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap_mem_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap_mem_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereMap_mem_cutCore

def cuttingSphereAttachment (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    CuttingSpheres ι → cutCore f :=
  fun p => ⟨cuttingSphereMap hδ f p, cuttingSphereMap_mem_cutCore hδ f hf hdisj p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereAttachment ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereAttachment

variable [TopologicalSpace M]

theorem continuous_cuttingSphereMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Continuous (f i)) :
    Continuous (cuttingSphereMap hδ f) := by
  apply continuous_sigma
  intro b
  change Continuous (fun y : S2 => f b.1
    ⟨(y, cuttingSign b.2), offset_mem_bufferedCylinder (hδ b.1) (cuttingSign_sq b.2) y⟩)
  apply (hf b.1).comp
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_cuttingSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_cuttingSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_cuttingSphereMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_cuttingSphereMap

theorem isClosedEmbedding_cuttingSphereAttachment [Finite ι] [T2Space M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Topology.IsClosedEmbedding (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
  have hc : Continuous (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) :=
    (continuous_cuttingSphereMap hδ f (fun i => (hf i).continuous)).subtype_mk _
  apply hc.isClosedEmbedding
  intro p q he
  exact injective_cuttingSphereMap hδ f (fun i => (hf i).injective) hdisj (congrArg Subtype.val he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_cuttingSphereAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_cuttingSphereAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_cuttingSphereAttachment ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_cuttingSphereAttachment

theorem range_cuttingSphereAttachment [Finite ι] [T2Space M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Set.range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) =
      {x : cutCore f | x.val ∈ frontier (cutCore f)} := by
  ext x
  rw [frontier_cutCore hδ f hf hdisj, ← range_cuttingSphereMap hδ f]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereAttachment ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_cuttingSphereAttachment
end DifferentialGeometry.Topology.ThreeManifold.Surgery
