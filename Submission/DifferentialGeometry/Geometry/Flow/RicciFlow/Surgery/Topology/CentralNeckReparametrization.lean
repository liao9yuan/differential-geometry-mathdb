import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRotationCutCore

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type*} {ι : Type*} {δ : ι → ℝ}

theorem removedSlab_eq_of_central_sphere_reparametrization {d : ℝ}
    {f g : bufferedCylinder d → M}
    (e : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2)
    (hmap : ∀ z ∈ centralDomain d, g z = f ⟨(e z.val.1, z.val.2), z.property⟩) :
    removedSlab g = removedSlab f := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨(e z.val.1, z.val.2), z.property⟩, hz, (hmap z hz).symm⟩
  · rintro _ ⟨z, hz, rfl⟩
    let w : bufferedCylinder d := ⟨(e.symm z.val.1, z.val.2), z.property⟩
    refine ⟨w, hz, ?_⟩
    rw [hmap w hz]
    apply congrArg f
    exact Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_central_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_central_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_central_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.removedSlab_eq_of_central_sphere_reparametrization

theorem cutCore_eq_of_central_sphere_reparametrization
    {f g : ∀ i : ι, bufferedCylinder (δ i) → M}
    (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
    (hmap : ∀ i z, z ∈ centralDomain (δ i) → g i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩) :
    cutCore g = cutCore f := by
  unfold cutCore
  congr 1
  exact _root_.Set.iUnion_congr fun i => removedSlab_eq_of_central_sphere_reparametrization (e i) (hmap i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_central_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_central_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_central_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_of_central_sphere_reparametrization

section Scalar
variable [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]
  {f g : ∀ i : ι, bufferedCylinder (δ i) → M}

theorem mem_scalarSublevelComponents_of_cutCore_eq
    (U : _root_.TopologicalSpace.Opens M) (metric : DifferentialGeometry.SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore g = cutCore f) (x : cutCore g) :
    ConnectedComponents.mk x ∈ scalarSublevelComponents U metric g K ↔
      ConnectedComponents.mk (Homeomorph.setCongr hcore x) ∈ scalarSublevelComponents U metric f K := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U metric K hcore]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.mem_scalarSublevelComponents_of_cutCore_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.mem_scalarSublevelComponents_of_cutCore_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.mem_scalarSublevelComponents_of_cutCore_eq ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.mem_scalarSublevelComponents_of_cutCore_eq

end Scalar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
