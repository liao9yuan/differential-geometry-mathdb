import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ} {L : ℝ}

def coreInteriorDomain (f : ∀ i : ι, bufferedCylinder (precision i) → M) : _root_.TopologicalSpace.Opens M :=
  ⟨interior (cutCore f), isOpen_interior⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorDomain

def finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    coreInteriorDomain f → FiniteCapQuotient hL hδ f hf hdisj :=
  fun p => finiteCoreInclusion hL hδ f hf hdisj ⟨p.val, interior_subset p.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap

theorem finiteCoreInteriorMap_apply (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) (p : coreInteriorDomain f) :
    finiteCoreInteriorMap hL hδ f hf hdisj p =
      finiteCoreInclusion hL hδ f hf hdisj ⟨p.val, interior_subset p.property⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_apply

theorem range_finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    range (finiteCoreInteriorMap hL hδ f hf hdisj) = finiteCoreInterior hL hδ f hf hdisj := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.val, interior_subset p.property⟩, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p.val, hp⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCoreInteriorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCoreInteriorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCoreInteriorMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCoreInteriorMap

variable [Finite ι] [T2Space M]

theorem isOpenEmbedding_finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Topology.IsOpenEmbedding (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) := by
  have hi : _root_.Topology.IsEmbedding (fun p : coreInteriorDomain f =>
      (⟨p.val, interior_subset p.property⟩ : cutCore f)) :=
    _root_.Topology.IsEmbedding.subtypeVal.codRestrict (cutCore f) (fun p => interior_subset p.property)
  refine ⟨(isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding.comp hi, ?_⟩
  rw [range_finiteCoreInteriorMap]
  exact isOpen_finiteCoreInterior hL hδ f hf hdisj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_finiteCoreInteriorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_finiteCoreInteriorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_finiteCoreInteriorMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_finiteCoreInteriorMap

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "old" => finiteCoreInteriorMap hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreOpenChart (x : coreInteriorDomain f) : OpenPartialHomeomorph Q H := by
  let : Nonempty H := ⟨chartAt H x x⟩
  exact (chartAt H x).lift_openEmbedding (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart

theorem finiteCoreOpenChart_source (x : coreInteriorDomain f) :
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source = old '' (chartAt H x).source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source

theorem finiteCoreOpenChart_target (x : coreInteriorDomain f) :
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).target = (chartAt H x).target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_target ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_target

theorem finiteCoreOpenChart_apply (x p : coreInteriorDomain f) :
    finiteCoreOpenChart (H := H) hL hδ f hf hdisj x (old p) = chartAt H x.val p.val := by
  let : Nonempty H := ⟨chartAt H x x⟩
  rw [finiteCoreOpenChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_apply

theorem finiteCoreOpenChart_source_cover :
    (⋃ x : coreInteriorDomain f, (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source) =
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
  rw [← range_finiteCoreInteriorMap]
  ext q
  constructor
  · intro hq
    obtain ⟨x, p, _, hp⟩ := mem_iUnion.mp hq
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, p, mem_chart_source H p, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_source_cover
end DifferentialGeometry.Topology.ThreeManifold.Surgery
