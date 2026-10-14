/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutPair
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocalDiskSeparation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskContainment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsPLSphere.exists_return_disk_avoiding_family
    {S L Lb B : Set E} (hS : IsPLSphere 2 S)
    {p : (Fin 3 → ℝ) → E} (hp : IsPLHomeomorphOn p (stdSimplex ℝ (Fin 3)) L)
    (hpLb : p '' stdSimplexBoundary 2 = Lb) (hLS : L ⊆ S)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (_root_.Set.Icc 0 1) B) (hBS : B ⊆ S)
    (hends : ({η 0, η 1} : Set E) ⊆ Lb) (hBL : B ∩ L = {η 0, η 1})
    {ι : Type*} (F : ι → Set E)
    (hconnect : ∀ R : Set E, IsPLSphere 1 (B ∪ R) → R ⊆ Lb →
      ∃ Y : Set E, IsConnected Y ∧ Y ⊆ S \ (B ∪ R) ∧ ∀ i, F i ∩ S ⊆ Y) :
    ∃ (R D : Set E) (q : (Fin 3 → ℝ) → E) (δ : ℝ → E),
      IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
      R ⊆ Lb ∧ B ∩ R = {η 0, η 1} ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧
      q '' stdSimplexBoundary 2 = B ∪ R ∧ D ⊆ S ∧ D ∩ L = R ∧
      ∀ i, Disjoint D (F i) := by
  have hη0 : η 0 ∈ B := hη.bijOn.mapsTo (by norm_num)
  have hη1 : η 1 ∈ B := hη.bijOn.mapsTo (by norm_num)
  have hLbL : Lb ⊆ L := by
    rw [← hpLb, ← hp.image_eq]
    exact _root_.Set.image_mono fun x hx => hx.1
  have hL : IsPLBall 2 L := ⟨p, hp⟩
  let Q := closure (S \ L)
  have hQS : Q ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  obtain ⟨r, hr⟩ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff hL hLS
  have hQLb : Q ∩ L = Lb := by
    rw [_root_.Set.inter_comm]
    exact (hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hp hLS).trans hpLb
  have hrLb : r '' stdSimplexBoundary 2 = Lb :=
    (hS.image_stdSimplexBoundary_complement hL hLS hr).trans hQLb
  have hBQ : B ⊆ Q := by
    change B ⊆ closure (S \ L)
    rw [hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hp hLS, hpLb]
    intro x hxB
    exact ⟨hBS hxB, fun hxL => hxL.2 (hends (hBL.subset ⟨hxB, hxL.1⟩))⟩
  have hBLb : B ∩ Lb = {η 0, η 1} := Subset.antisymm
    (fun x hx => hBL.subset ⟨hx.1, hLbL hx.2⟩)
    (fun x hx => ⟨(_root_.Set.pair_subset hη0 hη1) hx, hends hx⟩)
  obtain ⟨D₁, D₂, R₁, R₂, q₁, q₂, δ₁, δ₂, hq₁, hq₂, hδ₁, hδ₂,
    hδ₁0, hδ₁1, hδ₂0, hδ₂1, hDunion, hDinter, hq₁B, hq₂B, hD₁R, hD₂R,
    hRunion, -⟩ :=
    exists_disk_pair_with_boundary_arcs_of_proper_arc hr hη hBQ (by rw [hrLb]; exact hBLb)
  rw [hrLb] at hD₁R hD₂R hRunion
  have hD₁Q : D₁ ⊆ Q := subset_union_left.trans hDunion.subset
  have hD₂Q : D₂ ⊆ Q := subset_union_right.trans hDunion.subset
  have hR₁Lb : R₁ ⊆ Lb := subset_union_left.trans hRunion.subset
  have hJ : IsPLSphere 1 (B ∪ R₁) := hq₁B ▸ hq₁.isPLSphere_image_stdSimplexBoundary
  obtain ⟨Y, hY, hYS, hFY⟩ := hconnect R₁ hJ hR₁Lb
  have hselect : ∀ (D R : Set E) (q : (Fin 3 → ℝ) → E) (δ : ℝ → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D →
      IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) R → δ 0 = η 0 → δ 1 = η 1 →
      D ⊆ Q → q '' stdSimplexBoundary 2 = B ∪ R → D ∩ Lb = R → Disjoint D Y →
      ∃ (R D : Set E) (q : (Fin 3 → ℝ) → E) (δ : ℝ → E),
        IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
        R ⊆ Lb ∧ B ∩ R = {η 0, η 1} ∧
        IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧
        q '' stdSimplexBoundary 2 = B ∪ R ∧ D ⊆ S ∧ D ∩ L = R ∧
        ∀ i, Disjoint D (F i) := by
    intro D R q δ hq hδ hδ0 hδ1 hDQ hqB hDR hDY
    have hDS := hDQ.trans hQS
    have hRLb := hDR.symm.subset.trans _root_.Set.inter_subset_right
    have hRends : ({η 0, η 1} : Set E) ⊆ R := by
      rw [← hδ0, ← hδ1]
      exact _root_.Set.pair_subset (hδ.bijOn.mapsTo (by norm_num)) (hδ.bijOn.mapsTo (by norm_num))
    have hBR : B ∩ R = {η 0, η 1} := Subset.antisymm
      (fun x hx => hBLb.subset ⟨hx.1, hRLb hx.2⟩)
      (fun x hx => ⟨(_root_.Set.pair_subset hη0 hη1) hx, hRends hx⟩)
    have hDL : D ∩ L = R := by
      calc D ∩ L = D ∩ (Q ∩ L) := by
            rw [← _root_.Set.inter_assoc, inter_eq_left.mpr hDQ]
        _ = D ∩ Lb := by rw [hQLb]
        _ = R := hDR
    refine ⟨R, D, q, δ, hδ, hδ0, hδ1, hRLb, hBR, hq, hqB, hDS, hDL, ?_⟩
    intro i
    exact disjoint_left.mpr fun x hxD hxF =>
      disjoint_left.mp hDY hxD (hFY i ⟨hxF, hDS hxD⟩)
  have hYJ : Disjoint Y (q₁ '' stdSimplexBoundary 2) := by
    rw [hq₁B]
    exact disjoint_left.mpr fun x hx hxJ => (hYS hx).2 hxJ
  rcases hS.subset_or_disjoint_disk_of_eventually_eq hq₁ (hD₁Q.trans hQS)
      (fun _ _ => Filter.Eventually.of_forall fun _ => Iff.rfl)
      hY.isPreconnected (hYS.trans _root_.Set.sdiff_subset) hYJ with hYD₁ | hD₁Y
  · have hD₂Y : Disjoint D₂ Y := by
      apply disjoint_left.mpr
      intro x hxD₂ hxY
      exact (hYS hxY).2 (Or.inl (hDinter.subset ⟨hYD₁ hxY, hxD₂⟩))
    exact hselect D₂ R₂ q₂ δ₂ hq₂ hδ₂ hδ₂0 hδ₂1 hD₂Q hq₂B hD₂R hD₂Y
  · exact hselect D₁ R₁ q₁ δ₁ hq₁ hδ₁ hδ₁0 hδ₁1 hD₁Q hq₁B hD₁R hD₁Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_return_disk_avoiding_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_return_disk_avoiding_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_return_disk_avoiding_family ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_return_disk_avoiding_family

end DifferentialGeometry.Topology.PiecewiseLinear
