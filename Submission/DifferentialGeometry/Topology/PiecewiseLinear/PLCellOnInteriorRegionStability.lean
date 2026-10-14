/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnThickeningStability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn
    {S B R K : Set M₁} {F : M₁ → M₂}
    (hS : IsPLCellOn 3 S B) (hFc : ContinuousOn F S) (hFi : _root_.Set.InjOn F S)
    (hRS : R ⊆ S) (hK : IsCompact K) (hKR : K ⊆ interior R) :
    ∃ δ > 0, ∀ G : M₁ → M₂, IsPLHomeomorphInto 3 G S →
      (∀ z ∈ S, _root_.Dist.dist (F z) (G z) < δ) →
      cthickening δ (F '' K) ⊆ interior (G '' R) := by
  have hKI : K ⊆ interior S := hKR.trans (interior_mono hRS)
  have hKS : K ⊆ S := hKI.trans interior_subset
  have hKB : K ⊆ S \ B := by
    rw [hS.sdiff_boundary_eq_interior]
    exact hKI
  obtain ⟨a, ha, hastable⟩ :=
    exists_cthickening_subset_image_interior_stable_of_isPLCellOn hS hFc hFi hK hKB
  have hdisj : Disjoint (F '' K) (F '' (S \ interior R)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := hFi (hKS hx) hz.1 (hxy.trans hzy.symm)
    exact hz.2 (hxz ▸ hKR hx)
  have hKc : IsCompact (F '' K) := hK.image_of_continuousOn (hFc.mono hKS)
  have hRc : IsClosed (F '' (S \ interior R)) :=
    ((hS.isCompact.diff isOpen_interior).image_of_continuousOn
      (hFc.mono _root_.Set.sdiff_subset)).isClosed
  obtain ⟨b, hb, hbdisj⟩ := hdisj.exists_cthickenings hKc hRc
  refine ⟨min a b, lt_min ha hb, fun G hG hclose y hy => ?_⟩
  have hGS : y ∈ interior (G '' S) :=
    hastable G hG (fun z hz => (hclose z hz).trans_le (min_le_left _ _))
      (_root_.Metric.cthickening_mono (min_le_left _ _) _ hy)
  obtain ⟨x, hx, hxy⟩ := interior_subset hGS
  have hxR : x ∈ interior R := by
    by_contra hxR
    have hyR : y ∈ _root_.Metric.cthickening b (F '' (S \ interior R)) := by
      rw [← hxy]
      apply _root_.Metric.thickening_subset_cthickening
      apply _root_.Metric.ball_subset_thickening (show F x ∈ F '' (S \ interior R) from
        _root_.Set.mem_image_of_mem F ⟨hx, hxR⟩)
      rw [Metric.mem_ball, dist_comm]
      exact (hclose x hx).trans_le (min_le_right _ _)
    exact Set.disjoint_left.mp hbdisj
      (_root_.Metric.cthickening_mono (min_le_right _ _) _ hy) hyR
  have hGo : IsOpen (G '' interior R) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      (hG.continuousOn.mono (interior_subset.trans hRS))
      (hG.injOn.mono (interior_subset.trans hRS))
  exact interior_maximal (_root_.Set.image_mono interior_subset) hGo ⟨x, hxR, hxy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn

end DifferentialGeometry.Topology.PiecewiseLinear
