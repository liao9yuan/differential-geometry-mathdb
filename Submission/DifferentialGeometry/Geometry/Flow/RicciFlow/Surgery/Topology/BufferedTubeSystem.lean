import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M]
    {ι : Type} [Fintype ι] {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
    (f : ∀ i : ι, bufferedCylinder (δ i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

def ofBufferedCharts : TubeSystem M where
  Index := ι
  finiteIndex := inferInstance
  tube i := ⟨f i ∘ tubeDomainToBufferedCylinder (δ i) (hδ i) (hδ1 i),
    (hf i).continuous.comp (continuous_tubeDomainToBufferedCylinder (δ i) (hδ i) (hδ1 i))⟩
  embedding i :=
    (hf i).isEmbedding.comp
      ((continuous_tubeDomainToBufferedCylinder (δ i) (hδ i) (hδ1 i)).isClosedEmbedding
        (tubeDomainToBufferedCylinder_injective (δ i) (hδ i) (hδ1 i))).isEmbedding
  disjoint := by
    intro i j hij
    exact (hdisj hij).mono
      (_root_.Set.range_comp_subset_range (tubeDomainToBufferedCylinder (δ i) (hδ i) (hδ1 i)) (f i))
      (_root_.Set.range_comp_subset_range (tubeDomainToBufferedCylinder (δ j) (hδ j) (hδ1 j)) (f j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts

@[simp] theorem ofBufferedCharts_tube (i : ι) :
    ((ofBufferedCharts hδ hδ1 f hf hdisj).tube i : TubeDomain → M) =
      originalTubularMap (hδ i) (hδ1 i) (f i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_tube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_tube

@[simp] theorem ofBufferedCharts_removedBand (i : ι) :
    (ofBufferedCharts hδ hδ1 f hf hdisj).removedBand i = removedSlab (f i) := by
  exact originalTubularMap_central_image (hδ i) (hδ1 i) (f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_removedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_removedBand

@[simp] theorem ofBufferedCharts_core :
    (ofBufferedCharts hδ hδ1 f hf hdisj).core = cutCore f := by
  change (⋃ i : ι, (ofBufferedCharts hδ hδ1 f hf hdisj).removedBand i)ᶜ = (⋃ i, removedSlab (f i))ᶜ
  congr 1
  exact _root_.Set.iUnion_congr fun i => ofBufferedCharts_removedBand hδ hδ1 f hf hdisj i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.ofBufferedCharts_core

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (Sphere)

variable {M : Type*} {ι : Type*} {δ : ι → ℝ}

theorem removedSlab_eq_of_sphere_reparametrization {d : ℝ}
    {f g : bufferedCylinder d → M} (e : Sphere 2 ≃ Sphere 2)
    (hmap : ∀ z, g z = f ⟨(e z.val.1, z.val.2), z.property⟩) :
    removedSlab g = removedSlab f := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨(e z.val.1, z.val.2), z.property⟩, hz, (hmap z).symm⟩
  · rintro _ ⟨z, hz, rfl⟩
    let w : bufferedCylinder d := ⟨(e.symm z.val.1, z.val.2), z.property⟩
    refine ⟨w, hz, ?_⟩
    rw [hmap]
    apply congrArg f
    exact Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_sphere_reparametrization

theorem cutCore_eq_of_sphere_reparametrization
    {f g : ∀ i : ι, bufferedCylinder (δ i) → M}
    (e : ι → (Sphere 2 ≃ Sphere 2))
    (hmap : ∀ i z, g i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩) :
    cutCore g = cutCore f := by
  unfold cutCore
  congr 1
  exact _root_.Set.iUnion_congr fun i => removedSlab_eq_of_sphere_reparametrization (e i) (hmap i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_sphere_reparametrization

end DifferentialGeometry.Topology.ThreeManifold.Surgery
