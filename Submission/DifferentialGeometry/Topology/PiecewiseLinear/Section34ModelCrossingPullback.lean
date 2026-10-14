import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossingNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelRegionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.hasPLCrossingAt_preimage_of_chart {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ interior P)
    {A B : Set M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hxc : u x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c (u x))) :
    HasPLCrossingAt (u ⁻¹' A) (u ⁻¹' B) x := by
  have huc := hu.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hx)
  have hn : interior P ∩ u ⁻¹' c.source ∈ 𝓝 x :=
    Filter.inter_mem (isOpen_interior.mem_nhds hx)
      (huc.preimage_mem_nhds (c.open_source.mem_nhds hxc))
  obtain ⟨D, hD, hDN, hxD⟩ := exists_isHPolytope_subset_mem_nhds hn
  have hDP : D ⊆ P := hDN.trans (inter_subset_left.trans interior_subset)
  have hDc : _root_.Set.MapsTo u D c.source := fun _ hy => (hDN hy).2
  have hpl : IsPLOn 3 3 (c ∘ u) D := by
    intro y hy
    exact (isPLAt_of_mem_maximalAtlas hc (hDc hy)).comp_isPLWithinAt
      (hu.isPLOn.mono_of_isPolyhedron hD.isPolyhedron hDP y hy)
  have hpa : IsPiecewiseAffineOn (c ∘ u) D := isPLOn_iff_isPiecewiseAffineOn.mp hpl
  have hinj : _root_.Set.InjOn (c ∘ u) D := by
    intro y hy z hz hyz
    exact hu.injOn (hDP hy) (hDP hz) (c.injOn (hDc hy) (hDc hz) hyz)
  have hhom := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD.isPolyhedron
    hpa hinj.bijOn_image
  have himage (S : Set M) : (c ∘ u) '' (D ∩ u ⁻¹' S) =
      (c ∘ u) '' D ∩ c '' (S ∩ c.source) := by
    apply Subset.antisymm
    · rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, u y, ⟨hyS, hDc hy⟩, rfl⟩
    · rintro _ ⟨⟨y, hy, rfl⟩, z, ⟨hzS, hzc⟩, hzy⟩
      have heq : z = u y := c.injOn hzc (hDc hy) hzy
      exact ⟨y, ⟨hy, show u y ∈ S from heq ▸ hzS⟩, rfl⟩
  exact HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds hhom hxD
    (himage A) (himage B) hcross

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.hasPLCrossingAt_preimage_of_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.hasPLCrossingAt_preimage_of_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.hasPLCrossingAt_preimage_of_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.hasPLCrossingAt_preimage_of_chart

end DifferentialGeometry.Topology.PiecewiseLinear
