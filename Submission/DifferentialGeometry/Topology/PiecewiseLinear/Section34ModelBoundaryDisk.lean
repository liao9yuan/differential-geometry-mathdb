import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryDiskNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_pseudo_cell_boundary_chart {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {S B D J : Set M}
    (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J) (hDB : D ⊆ B)
    (hDP : D ⊆ interior (u '' P)) :
    ∃ (E Eint Ebd : Set (EuclideanSpace ℝ (Fin 3))) (p : EuclideanSpace ℝ (Fin 3)),
      IsPseudoCell E Eint Ebd p ∧ E ⊆ P ∩ u ⁻¹' B ∧ E ⊆ interior P ∧
      Function.invFunOn u P '' D ⊆ Eint \ {p} ∧
      ∀ x ∈ Function.invFunOn u P '' D,
        ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ P ∩ u ⁻¹' B := by
  obtain ⟨E, L, p, hE, hEB, hDE, hpE, hpD, hgerm⟩ :=
    hS.exists_boundary_disk_neighborhood_of_disk hD hDB isOpen_interior hDP
  let τ := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτi : _root_.Set.InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hτint : _root_.Set.MapsTo τ (interior (u '' P)) (interior P) := by
    intro x hx
    rw [← hu.image_interior] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hleft (interior_subset hy)]
    exact hy
  have hEP : E ⊆ u '' P := fun _ hx => interior_subset (hEB hx).2
  have hDP' : D ⊆ u '' P := hDP.trans interior_subset
  obtain ⟨r, hr, hL⟩ := hE.exists_isPLHomeomorphOn_invFunOn hu hEP
  have hmapInt : τ '' (E \ L) = τ '' E \ r '' stdSimplexBoundary 2 := by
    rw [← hL]
    exact (hτi.mono hEP).image_sdiff_subset hE.boundary_subset
  have hpE' : τ p ∈ τ '' E \ r '' stdSimplexBoundary 2 :=
    hmapInt ▸ _root_.Set.mem_image_of_mem τ hpE
  have hDint : τ '' D ⊆ (τ '' E \ r '' stdSimplexBoundary 2) \ {τ p} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hmapInt ▸ _root_.Set.mem_image_of_mem τ (hDE hx), ?_⟩
    intro hxp
    exact hpD ((hτi (hDP' hx) (hEP hpE.1) hxp) ▸ hx)
  have hES : τ '' E ⊆ P ∩ u ⁻¹' B := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨interior_subset (hτint (hEB hx).2), ?_⟩
    change u (τ x) ∈ B
    rw [hright (hEP hx)]
    exact (hEB hx).1
  refine ⟨τ '' E, τ '' E \ r '' stdSimplexBoundary 2, r '' stdSimplexBoundary 2, τ p,
    hr.isPseudoCell_of_mem_interior hpE', hES, ?_, hDint, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hτint (hEB hx).2
  · rintro _ ⟨x, hx, rfl⟩
    have hxi := hτint (hDP hx)
    have hcont : ContinuousAt u (τ x) := (hu.continuousOn _ (interior_subset hxi)).continuousAt
      (mem_interior_iff_mem_nhds.mp hxi)
    have hg := hgerm x hx
    rw [← hright (hDP' hx)] at hg
    filter_upwards [hcont.eventually hg, mem_interior_iff_mem_nhds.mp hxi] with y hy hyP
    constructor
    · rintro ⟨z, hz, hzy⟩
      have huE : u y ∈ E := by rw [← hzy, hright (hEP hz)]; exact hz
      exact ⟨hyP, hy.mp huE⟩
    · intro hyB
      exact ⟨u y, hy.mpr hyB.2, hleft hyP⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_pseudo_cell_boundary_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_pseudo_cell_boundary_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_pseudo_cell_boundary_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_pseudo_cell_boundary_chart

end DifferentialGeometry.Topology.PiecewiseLinear
