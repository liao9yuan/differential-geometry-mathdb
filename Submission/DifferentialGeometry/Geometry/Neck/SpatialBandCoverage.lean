import Submission.DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem SpatialNeck.nonempty_at_of_mem_image_central_band
    {g : SmoothRiemannianMetric I3 M} {eps alpha : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) {x : M}
    (hx : x ∈ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-4 : ℝ) 4)) :
    Nonempty (SpatialNeck g alpha x) := by
  obtain ⟨⟨u, t⟩, ⟨_, ht⟩, hxt⟩ := hx
  obtain ⟨out, _⟩ := nk.exists_at_coordinate (a := t) hsmall hreserve u (by
    rw [abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact ⟨hxt.symm ▸ out⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.nonempty_at_of_mem_image_central_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.nonempty_at_of_mem_image_central_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.nonempty_at_of_mem_image_central_band ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.nonempty_at_of_mem_image_central_band

theorem nonempty_spatial_neck_of_subset_iUnion_central_bands
    {g : SmoothRiemannianMetric I3 M} {eps alpha : ℝ} {ι : Type*}
    (hsmall : alpha < 1 / 11) (hreserve : 13000 * eps ≤ alpha)
    (A : ι → Set M) (point : ι → M) (nk : ∀ i, SpatialNeck g eps (point i))
    (hcover : ∀ i, A i ⊆ (nk i).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-4 : ℝ) 4))
    {U : Set M} (hU : U ⊆ ⋃ i, A i) :
    ∀ x ∈ U, Nonempty (SpatialNeck g alpha x) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hU hx)
  exact (nk i).nonempty_at_of_mem_image_central_band hsmall hreserve (hcover i hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_spatial_neck_of_subset_iUnion_central_bands then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_spatial_neck_of_subset_iUnion_central_bands"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_spatial_neck_of_subset_iUnion_central_bands ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_spatial_neck_of_subset_iUnion_central_bands

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
