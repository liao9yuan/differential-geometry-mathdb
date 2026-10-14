import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskFillingTrace
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelRegionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.invFunOn_disk_filling_data {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {A Ab C D F J : Set M}
    (hA : IsPLCellOn 3 A Ab) (hAP : A ⊆ u '' P)
    (hC : IsPLCellOn 3 C (D ∪ F)) (hCP : C ⊆ u '' P)
    (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hmeet : Ab ∩ C = F) (htrace : D ∩ Ab = J) :
    let τ := Function.invFunOn u P
    IsPLSphere 2 (τ '' Ab) ∧ IsPLBall 3 (τ '' C) ∧
      IsPLBall 2 ((τ '' Ab) ∩ (τ '' C)) ∧
      (τ '' Ab) ∩ (τ '' C) ⊆ frontier (τ '' C) ∧
      closure (frontier (τ '' C) \ (τ '' Ab)) = τ '' D := by
  let τ := Function.invFunOn u P
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτi : _root_.Set.InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hAbP : Ab ⊆ u '' P := hA.boundary_subset.trans hAP
  have hDP : D ⊆ u '' P := (subset_union_left.trans hC.boundary_subset).trans hCP
  have hFP : F ⊆ u '' P := (subset_union_right.trans hC.boundary_subset).trans hCP
  obtain ⟨a, ha, haB⟩ := hA.exists_isPLHomeomorphOn_invFunOn hu hAP
  obtain ⟨c, hc, hcB⟩ := hC.exists_isPLHomeomorphOn_invFunOn hu hCP
  obtain ⟨d, hd, hdB⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  obtain ⟨f, hf, -⟩ := hF.exists_isPLHomeomorphOn_invFunOn hu hFP
  have hCfront : frontier (τ '' C) = (τ '' D) ∪ (τ '' F) := by
    rw [← hc.image_stdSimplexBoundary_eq_frontier, ← hcB, _root_.Set.image_union]
  have hmeet' : (τ '' Ab) ∩ (τ '' C) = τ '' F := by
    rw [← hτi.image_inter hAbP hCP, hmeet]
  have htrace' : (τ '' D) ∩ (τ '' Ab) = τ '' J := by
    rw [← hτi.image_inter hDP hAbP, htrace]
  have hFAb : τ '' F ⊆ τ '' Ab := _root_.Set.image_mono (hmeet ▸ _root_.Set.inter_subset_left)
  refine ⟨haB.symm ▸ ha.isPLSphere_image_stdSimplexBoundary, ⟨c, hc⟩,
    hmeet'.symm ▸ (show IsPLBall 2 (τ '' F) from ⟨f, hf⟩), ?_, ?_⟩
  · rw [hmeet', hCfront]
    exact _root_.Set.subset_union_right
  · have hdiff : frontier (τ '' C) \ (τ '' Ab) = (τ '' D) \ (τ '' J) := by
      rw [hCfront]
      ext x
      constructor
      · rintro ⟨hxD | hxF, hxAb⟩
        · exact ⟨hxD, fun hxJ => hxAb (htrace'.superset hxJ).2⟩
        · exact (hxAb (hFAb hxF)).elim
      · rintro ⟨hxD, hxJ⟩
        exact ⟨Or.inl hxD, fun hxAb => hxJ (htrace'.subset ⟨hxD, hxAb⟩)⟩
    rw [hdiff, hdB]
    exact hd.closure_sdiff_image_stdSimplexBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_disk_filling_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_disk_filling_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_disk_filling_data ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_disk_filling_data

end DifferentialGeometry.Topology.PiecewiseLinear
