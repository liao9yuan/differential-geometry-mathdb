/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.Separation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAnnulus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

namespace PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem moise303 : Moise303 := by
  intro M H K C Δ D₁ D₂ Ω r r₁ r₂ hM _ _ _ _ _ _ hCM hC hsep
    hr hΔC hr₁ hr₂ hmeet hDC hnear hΔ₁ hΔ₂ hΩ hΔΩ hΩM hΩHK
  let _ : LocallyPathConnectedSpace M := hM.locallyPathConnectedSpace
  obtain ⟨A₁, Δ₁, J₁, Q, O, J, S, r', ψ, hA, hAΩ, hAΔ, hr', hJ₁, hΔ₁Ω,
      hΔ₁C, hQ, hQΩ, hAQ, hΔ₁Q, hO, hCO, hJ, hψ, hfront, hsafe⟩ :=
    exists_annular_split_ball M C Δ D₁ D₂ Ω r r₁ r₂ hM hCM hC hr hΔC hr₁ hr₂
      hmeet hDC hnear hΔ₁ hΔ₂ hΩ hΔΩ hΩM
  let R := A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁)
  let C' := (C \ R) ∪ Δ₁
  have hremove : C \ R = C \ O := by
    change C \ (A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁)) = C \ O
    rw [← hCO]
    ext y
    simp only [_root_.Set.mem_sdiff, _root_.Set.mem_inter_iff]
    tauto
  have hC' : IsClosed (((↑) : M → E3) ⁻¹' C') := by
    change IsClosed (((↑) : M → E3) ⁻¹' ((C \ R) ∪ Δ₁))
    rw [hremove, _root_.Set.preimage_union, _root_.Set.preimage_sdiff]
    exact (hC.sdiff (hO.preimage continuous_subtype_val)).union
      ((show IsPLBall 2 Δ₁ from ⟨r', hr'⟩).isPolyhedron.isClosed.preimage
        continuous_subtype_val)
  have hC'M : C' ⊆ M := _root_.Set.union_subset (sdiff_subset.trans hCM) (hΔ₁Ω.trans hΩM)
  have hout : C \ Q = C' \ Q := by
    ext y
    constructor
    · rintro ⟨hyC, hyQ⟩
      exact ⟨Or.inl ⟨hyC, fun hyR => hyQ (hAQ hyR.1)⟩, hyQ⟩
    · rintro ⟨hy | hy, hyQ⟩
      · exact ⟨hy.1, hyQ⟩
      · exact (hyQ (hΔ₁Q hy)).elim
  have hC'Ω : C' \ Ω = C \ Ω := by
    ext y
    constructor
    · rintro ⟨hy | hy, hyΩ⟩
      · exact ⟨hy.1, hyΩ⟩
      · exact (hyΩ (hΔ₁Ω hy)).elim
    · rintro ⟨hyC, hyΩ⟩
      exact ⟨Or.inl ⟨hyC, fun hyR => hyΩ (hAΩ hyR.1).2⟩, hyΩ⟩
  have hD₂ : D₂ ⊆ C' := by
    intro y hy
    refine Or.inl ⟨hDC (Or.inr hy), ?_⟩
    intro hyR
    have hyΔ : y ∈ Δ := hmeet.subset ⟨(hAΩ hyR.1).1, hy⟩
    exact hyR.2 (Or.inl (hAΔ.subset ⟨hyR.1, hyΔ⟩))
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isClosed
  have hfrontM : frontier (((↑) : M → E3) ⁻¹' Q) \ (((↑) : M → E3) ⁻¹' C') =
      ((↑) : M → E3) ⁻¹' (frontier Q \ C') := by
    rw [← hM.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val Q, _root_.Set.preimage_sdiff]
  change frontier Q \ C' = ψ '' (J ×ˢ _root_.Set.Ioo (0 : ℝ) 1) at hfront
  have hfrontPath : IsPathConnected (frontier Q \ C') := by
    rw [hfront]
    exact (hJ.isPathConnected_one.prod
      ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩)).image'
      (hψ.isPiecewiseAffineOn.continuousOn.mono (_root_.Set.prod_mono Subset.rfl _root_.Set.Ioo_subset_Icc_self))
  have hpath : IsPathConnected
      (frontier (((↑) : M → E3) ⁻¹' Q) \ (((↑) : M → E3) ⁻¹' C')) := by
    rw [hfrontM]
    exact hfrontPath.preimage_coe
      (sdiff_subset.trans (hQclosed.frontier_subset.trans (hQΩ.trans hΩM)))
  have hfrontSafe : frontier (((↑) : M → E3) ⁻¹' Q) \ (((↑) : M → E3) ⁻¹' C') ⊆
      (((↑) : M → E3) ⁻¹' C)ᶜ := by
    rw [hfrontM, hfront]
    intro y hy hyC
    exact disjoint_left.mp hsafe hy hyC
  have houtM : (((↑) : M → E3) ⁻¹' C) \ (((↑) : M → E3) ⁻¹' Q) =
      (((↑) : M → E3) ⁻¹' C') \ (((↑) : M → E3) ⁻¹' Q) := by
    rw [← _root_.Set.preimage_sdiff, ← _root_.Set.preimage_sdiff, hout]
  have hHQ : (((↑) : M → E3) ⁻¹' H) ⊆ (((↑) : M → E3) ⁻¹' Q)ᶜ :=
    fun _ hy hyQ => disjoint_left.mp hΩHK (hQΩ hyQ) (Or.inl hy)
  have hKQ : (((↑) : M → E3) ⁻¹' K) ⊆ (((↑) : M → E3) ⁻¹' Q)ᶜ :=
    fun _ hy hyQ => disjoint_left.mp hΩHK (hQΩ hyQ) (Or.inr hy)
  have hHC' : (((↑) : M → E3) ⁻¹' H) ⊆ (((↑) : M → E3) ⁻¹' C')ᶜ := by
    intro y hy hyC'
    have hyout : y ∈ (((↑) : M → E3) ⁻¹' C') \ (((↑) : M → E3) ⁻¹' Q) :=
      ⟨hyC', hHQ hy⟩
    rw [← houtM] at hyout
    exact hsep.left_subset_compl hy hyout.1
  have hKC' : (((↑) : M → E3) ⁻¹' K) ⊆ (((↑) : M → E3) ⁻¹' C')ᶜ := by
    intro y hy hyC'
    have hyout : y ∈ (((↑) : M → E3) ⁻¹' C') \ (((↑) : M → E3) ⁻¹' Q) :=
      ⟨hyC', hKQ hy⟩
    rw [← houtM] at hyout
    exact hsep.right_subset_compl hy hyout.1
  refine ⟨C', A₁, Δ₁, J₁, r', hC', hC'M, ?_, hC'Ω, hD₂, hA, hAΩ, hAΔ,
    hr', hJ₁, hΔ₁Ω, hΔ₁C, rfl⟩
  apply separates_of_not_joinedIn hC' hHC' hKC'
  intro x hx y hy hjoined
  have hjoined' := JoinedIn.compl_of_frontier_replacement hjoined
    (hQclosed.preimage continuous_subtype_val) houtM hfrontSafe hpath (hHQ hx) (hKQ hy)
  exact hsep.not_mem_connectedComponentIn hx hy
    ((isConnected_range hjoined'.somePath.continuous).isPreconnected.subset_connectedComponentIn
      ⟨0, hjoined'.somePath.source⟩ (range_subset_iff.mpr hjoined'.somePath_mem)
      ⟨1, hjoined'.somePath.target⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise303 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise303"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise303 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise303

end PiecewiseLinear

end DifferentialGeometry.Topology
