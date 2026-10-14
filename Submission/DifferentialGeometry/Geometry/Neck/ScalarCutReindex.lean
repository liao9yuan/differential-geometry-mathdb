import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.Reindex
import Submission.DifferentialGeometry.Geometry.Neck.ScalarRetainedCore

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {M : Type*} [TopologicalSpace M] {ι κ : Type*} {δ : ι → ℝ}
  (f : ∀ i, bufferedCylinder (δ i) → M) (e : κ ≃ ι)
  (hδ : ∀ i, 0 < δ i) (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
section Scalar
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalarSublevelComponents_preimage_reindex
    (U : _root_.TopologicalSpace.Opens M) (g : DifferentialGeometry.SmoothRiemannianMetric I U) (K : ℝ) :
    scalarSublevelComponents U g (fun j => f (e j)) K =
      (Homeomorph.setCongr (cutCore_reindex f e)).continuous.connectedComponentsMap ⁻¹'
        scalarSublevelComponents U g f K :=
by
  let hcore := cutCore_reindex f e
  let ec := Homeomorph.setCongr hcore
  have hinj : _root_.Function.Injective ec.continuous.connectedComponentsMap := by
    intro a b hab
    have he (a : ConnectedComponents (cutCore (fun j => f (e j)))) :
        ec.symm.continuous.connectedComponentsMap (ec.continuous.connectedComponentsMap a) = a := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      change ConnectedComponents.mk (ec.symm (ec x)) = ConnectedComponents.mk x
      rw [ec.symm_apply_apply]
    have hh := congrArg ec.symm.continuous.connectedComponentsMap hab
    rw [he, he] at hh
    exact hh
  ext a
  constructor
  · rintro ⟨x, hx, hm, he⟩
    refine ⟨x, hx, hcore ▸ hm, ?_⟩
    rw [← he]
    rfl
  · rintro ⟨x, hx, hm, he⟩
    refine ⟨x, hx, hcore.symm ▸ hm, ?_⟩
    apply hinj
    exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_reindex

theorem retainedCore_image_reindex
    (U : _root_.TopologicalSpace.Opens M) (g : DifferentialGeometry.SmoothRiemannianMetric I U) (K : ℝ) :
    (Subtype.val : cutCore (fun j => f (e j)) → M) ''
      retainedCore (fun j => f (e j)) (scalarSublevelComponents U g (fun j => f (e j)) K) =
      (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f K) :=
by
  rw [scalarSublevelComponents_preimage_reindex f e U g K]
  let ec := Homeomorph.setCongr (cutCore_reindex f e)
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨ec p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨ec.symm p, ?_, rfl⟩
    change ConnectedComponents.mk (ec (ec.symm p)) ∈ scalarSublevelComponents U g f K
    rw [ec.apply_symm_apply]
    exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_reindex

theorem cuttingSphereComponent_mem_reindex
    (U : _root_.TopologicalSpace.Opens M) (g : DifferentialGeometry.SmoothRiemannianMetric I U) (K : ℝ) (b : κ × Bool) :
    cuttingSphereComponent (fun j => hδ (e j)) (fun j => f (e j)) (fun j => hf (e j))
      (pairwise_disjoint_reindex f e hdisj) b ∈ scalarSublevelComponents U g (fun j => f (e j)) K ↔
      cuttingSphereComponent hδ f hf hdisj (e b.1, b.2) ∈ scalarSublevelComponents U g f K := by
  rw [scalarSublevelComponents_preimage_reindex f e U g K]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_reindex

end Scalar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
