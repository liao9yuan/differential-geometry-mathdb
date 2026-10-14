import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SphereDiskNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_boundary_disk_neighborhood_of_disk {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D J Ω : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J)
    (hDB : D ⊆ B) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ (E L : Set M) (p : M), IsPLCellOn 2 E L ∧ E ⊆ B ∩ Ω ∧
      D ⊆ E \ L ∧ p ∈ E \ L ∧ p ∉ D ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ B := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hDP : D ⊆ u '' P := hDB.trans (hB ▸ _root_.Set.image_mono hfront)
  let δ := Function.invFunOn u P '' D
  obtain ⟨q, hq, -⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  have hδ : IsPLBall 2 δ := ⟨q, hq⟩
  have hδS : δ ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hDB hx
    rw [hu.injOn.leftInvOn_invFunOn (hfront hz)]
    exact hz
  have hback : u '' δ = D := by
    rw [_root_.Set.image_image]
    exact (_root_.Set.image_congr fun x hx => hu.injOn.bijOn_image.invOn_invFunOn.2 (hDP hx)).trans
      (_root_.Set.image_id' D)
  obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.mp hu.continuousOn Ω hΩ
  have hδV : δ ⊆ V := fun _ hx => (hVeq.subset
    ⟨hDΩ (hback ▸ _root_.Set.mem_image_of_mem u hx), hfront (hδS hx)⟩).1
  obtain ⟨E, s, hs, hES, hδE, hgerm⟩ :=
    hP.isPLSphere_frontier.exists_disk_neighborhood_of_disk_subset hδ hδS hV hδV
  obtain ⟨p, hpE, hpδ⟩ :=
    hs.exists_interior_point_outside_closed_disk_subset hδ.isPolyhedron.isClosed hδE
  have hEP : E ⊆ P := hES.trans (inter_subset_left.trans hfront)
  have hE : IsPLBall 2 E := ⟨s, hs⟩
  have huE : IsPLHomeomorphInto 3 u E :=
    (hu.isPLOn.mono_of_isPolyhedron hE.isPolyhedron hEP).isPLHomeomorphInto_model
      hE.isPolyhedron.isCompact (hu.injOn.mono hEP)
  have hLE : s '' stdSimplexBoundary 2 ⊆ E :=
    hs.image_eq ▸ _root_.Set.image_mono (fun _ hx => hx.1)
  have hδEL : δ ⊆ E \ s '' stdSimplexBoundary 2 := by
    rwa [← hs.image_openSimplex_stdVertices]
  have hmapInt : u '' (E \ s '' stdSimplexBoundary 2) =
      u '' E \ u '' (s '' stdSimplexBoundary 2) :=
    (hu.injOn.mono hEP).image_sdiff_subset hLE
  let W := {x | ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ frontier P}
  have hW : IsOpen W := isOpen_setOfPred_eventually_nhds
  have houtside : IsCompact (u '' (frontier P \ W)) :=
    (hP.isPLSphere_frontier.isPolyhedron.isCompact.diff hW).image_of_continuousOn
      (hu.continuousOn.mono (sdiff_subset.trans hfront))
  have havoid : D ⊆ (u '' (frontier P \ W))ᶜ := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hback.superset hx
    rintro ⟨z, hz, hzw⟩
    have heq := hu.injOn (hfront hz.1) (hfront (hδS hw)) hzw
    exact hz.2 (heq.symm ▸ hgerm w hw)
  refine ⟨u '' E, u '' (s '' stdSimplexBoundary 2), u p,
    (isPLCellOn_id_of_isPLBall hs).image huE, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨hB.symm ▸ _root_.Set.mem_image_of_mem u (hES hz).1,
      (hVeq.superset ⟨(hES hz).2, hEP hz⟩).1⟩
  · rw [← hmapInt, ← hback]
    exact _root_.Set.image_mono hδEL
  · exact hmapInt ▸ _root_.Set.mem_image_of_mem u hpE
  · intro hpD
    obtain ⟨w, hw, hwp⟩ := hback.superset hpD
    exact hpδ ((hu.injOn (hfront (hδS hw)) (hEP hpE.1) hwp) ▸ hw)
  · intro x hx
    filter_upwards [houtside.isClosed.isOpen_compl.mem_nhds (havoid hx)] with y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hB.symm ▸ _root_.Set.mem_image_of_mem u (hES hz).1
    · intro hyB
      obtain ⟨z, hz, rfl⟩ := hB.subset hyB
      have hzW : z ∈ W := by
        by_contra hn
        exact hy ⟨z, ⟨hz, hn⟩, rfl⟩
      exact ⟨z, hzW.self_of_nhds.mpr hz, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_neighborhood_of_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_neighborhood_of_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_neighborhood_of_disk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_neighborhood_of_disk

end DifferentialGeometry.Topology.PiecewiseLinear
