import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

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

omit [TopologicalSpace M] in
theorem cutCore_reindex : cutCore (fun j => f (e j)) = cutCore f := by
  unfold cutCore
  congr 1
  exact _root_.Set.iUnion_congr_of_surjective e e.surjective (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_reindex

omit [TopologicalSpace M] in
theorem pairwise_disjoint_reindex
    (hdisj : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))) :
    Pairwise fun i j => Disjoint (_root_.Set.range (f (e i))) (_root_.Set.range (f (e j))) :=
  fun _ _ hij => hdisj (fun h => hij (e.injective h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_reindex

variable (hδ : ∀ i, 0 < δ i) (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

theorem cuttingSphereComponent_map_reindex (b : κ × Bool) :
    (Homeomorph.setCongr (cutCore_reindex f e)).continuous.connectedComponentsMap
      (cuttingSphereComponent (fun j => hδ (e j)) (fun j => f (e j)) (fun j => hf (e j))
        (pairwise_disjoint_reindex f e hdisj) b) =
      cuttingSphereComponent hδ f hf hdisj (e b.1, b.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_reindex ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_reindex

end DifferentialGeometry.Topology.ThreeManifold.Surgery
