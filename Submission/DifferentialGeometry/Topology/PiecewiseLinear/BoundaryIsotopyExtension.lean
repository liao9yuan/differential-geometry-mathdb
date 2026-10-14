/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.Homeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_homeomorph_of_boundary_isotopy
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (G : ℝ → BoundaryManifold (𝓡∂ 3) M ≃ₜ BoundaryManifold (𝓡∂ 3) M)
    (hG : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => G p.1 p.2))
    (hGi : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => (G p.1).symm p.2))
    (hG0 : G 0 = Homeomorph.refl _) :
    ∃ θ : M ≃ₜ M, θ '' (𝓡∂ 3).boundary M = (𝓡∂ 3).boundary M ∧
      ∀ b : BoundaryManifold (𝓡∂ 3) M, θ b.val = (G 1 b).val := by
  classical
  let B := BoundaryManifold (𝓡∂ 3) M
  have hK : IsCompact ((𝓡∂ 3).boundary M) :=
    ((𝓡∂ 3).isClosed_boundary (n := ∞) (by simp)).isCompact
  have hBc : CompactSpace B := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, U, -, e, he0, -⟩ :=
    DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_collar_homeomorph
      (n := 2) (M := M) hK
  let φ : ℝ → ℝ := fun t => _root_.Max.max 0 (1 - 2 * t / δ)
  have hφc : Continuous φ := continuous_const.max
    (continuous_const.sub ((continuous_const.mul continuous_id).div_const δ))
  have hφ0 : φ 0 = 1 := by simp [φ]
  have hφ1 : ∀ t : ℝ, δ / 2 < t → φ t = 0 := by
    intro t ht
    apply max_eq_left
    have h1 : 1 < 2 * t / δ := by
      rw [lt_div_iff₀ hδ]
      linarith
    linarith
  let F : B × _root_.Set.Ico (0 : ℝ) δ → B × _root_.Set.Ico (0 : ℝ) δ := fun q => (G (φ q.2) q.1, q.2)
  let Fi : B × _root_.Set.Ico (0 : ℝ) δ → B × _root_.Set.Ico (0 : ℝ) δ := fun q => ((G (φ q.2)).symm q.1, q.2)
  have hFc : Continuous F :=
    (hG.comp ((hφc.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      continuous_fst)).prodMk continuous_snd
  have hFic : Continuous Fi :=
    (hGi.comp ((hφc.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      continuous_fst)).prodMk continuous_snd
  have hFFi : ∀ q, F (Fi q) = q := by
    intro q
    exact Prod.ext ((G (φ q.2)).apply_symm_apply q.1) rfl
  have hFiF : ∀ q, Fi (F q) = q := by
    intro q
    exact Prod.ext ((G (φ q.2)).symm_apply_apply q.1) rfl
  have hFid : ∀ q : B × _root_.Set.Ico (0 : ℝ) δ, δ / 2 < (q.2 : ℝ) → F q = q ∧ Fi q = q := by
    intro q hq
    have h := hφ1 _ hq
    have hG0' : G (φ q.2) = Homeomorph.refl B := by rw [h, hG0]
    constructor
    · refine Prod.ext ?_ rfl
      change G (φ q.2) q.1 = q.1
      rw [hG0']
      rfl
    · refine Prod.ext ?_ rfl
      change (G (φ q.2)).symm q.1 = q.1
      rw [hG0']
      rfl
  let T : Set M := (fun q => (e q : M)) '' {q : B × _root_.Set.Ico (0 : ℝ) δ | (q.2 : ℝ) ≤ δ / 2}
  have hTc : IsClosed T := by
    have hcomp : IsCompact {q : B × _root_.Set.Ico (0 : ℝ) δ | (q.2 : ℝ) ≤ δ / 2} := by
      have heq : {q : B × _root_.Set.Ico (0 : ℝ) δ | (q.2 : ℝ) ≤ δ / 2} =
          univ ×ˢ ((Subtype.val : _root_.Set.Ico (0 : ℝ) δ → ℝ) ⁻¹' _root_.Set.Icc 0 (δ / 2)) := by
        ext q
        simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_prod, _root_.Set.mem_univ, _root_.Set.mem_preimage, _root_.Set.mem_Icc, true_and]
        exact ⟨fun h => ⟨q.2.2.1, h⟩, fun h => h.2⟩
      rw [heq]
      refine isCompact_univ.prod ?_
      have hemb : _root_.Topology.IsClosedEmbedding (fun t : _root_.Set.Icc (0 : ℝ) (δ / 2) =>
          (⟨t.val, t.2.1, by linarith [t.2.2]⟩ : _root_.Set.Ico (0 : ℝ) δ)) :=
        (Continuous.subtype_mk continuous_subtype_val _).isClosedEmbedding (by
          intro a b h
          exact Subtype.ext (congrArg (fun x : _root_.Set.Ico (0 : ℝ) δ => x.val) h))
      have hrange : _root_.Set.range (fun t : _root_.Set.Icc (0 : ℝ) (δ / 2) =>
          (⟨t.val, t.2.1, by linarith [t.2.2]⟩ : _root_.Set.Ico (0 : ℝ) δ)) =
          (Subtype.val : _root_.Set.Ico (0 : ℝ) δ → ℝ) ⁻¹' _root_.Set.Icc 0 (δ / 2) := by
        ext t
        constructor
        · rintro ⟨s, rfl⟩
          exact s.2
        · intro ht
          exact ⟨⟨t.val, ht⟩, rfl⟩
      rw [← hrange]
      exact isCompact_range hemb.continuous
    exact (hcomp.image (continuous_subtype_val.comp e.continuous)).isClosed
  have hTU : ∀ m ∈ T, m ∈ (U : Set M) := by
    rintro _ ⟨q, -, rfl⟩
    exact (e q).2
  let θf : M → M := fun m => if h : m ∈ (U : Set M) then (e (F (e.symm ⟨m, h⟩)) : M) else m
  let θi : M → M := fun m => if h : m ∈ (U : Set M) then (e (Fi (e.symm ⟨m, h⟩)) : M) else m
  have hθf_on : ∀ q, θf (e q) = e (F q) := by
    intro q
    simp only [θf, Subtype.coe_eta, e.symm_apply_apply]
    exact dif_pos (e q).2
  have hθi_on : ∀ q, θi (e q) = e (Fi q) := by
    intro q
    simp only [θi, Subtype.coe_eta, e.symm_apply_apply]
    exact dif_pos (e q).2
  have hθf_off : ∀ m, m ∉ T → θf m = m := by
    intro m hm
    by_cases hU : m ∈ (U : Set M)
    · have hq : ¬ ((e.symm ⟨m, hU⟩).2 : ℝ) ≤ δ / 2 := by
        intro h
        apply hm
        refine ⟨e.symm ⟨m, hU⟩, h, ?_⟩
        change (e (e.symm ⟨m, hU⟩) : M) = m
        rw [e.apply_symm_apply]
      simp only [θf, dif_pos hU]
      rw [(hFid _ (not_le.mp hq)).1, e.apply_symm_apply]
    · simp only [θf, dif_neg hU]
  have hθi_off : ∀ m, m ∉ T → θi m = m := by
    intro m hm
    by_cases hU : m ∈ (U : Set M)
    · have hq : ¬ ((e.symm ⟨m, hU⟩).2 : ℝ) ≤ δ / 2 := by
        intro h
        apply hm
        refine ⟨e.symm ⟨m, hU⟩, h, ?_⟩
        change (e (e.symm ⟨m, hU⟩) : M) = m
        rw [e.apply_symm_apply]
      simp only [θi, dif_pos hU]
      rw [(hFid _ (not_le.mp hq)).2, e.apply_symm_apply]
    · simp only [θi, dif_neg hU]
  have hcont : ∀ (H : B × _root_.Set.Ico (0 : ℝ) δ → B × _root_.Set.Ico (0 : ℝ) δ), Continuous H →
      ∀ θ : M → M, (∀ q, θ (e q) = e (H q)) → (∀ m, m ∉ T → θ m = m) → Continuous θ := by
    intro H hH θ hon hoff
    rw [continuous_iff_continuousAt]
    intro m
    by_cases hm : m ∈ T
    · have hU := hTU m hm
      have hloc : ContinuousAt (fun m' : M => if h : m' ∈ (U : Set M) then
          (e (H (e.symm ⟨m', h⟩)) : M) else m') m := by
        have hc : ContinuousOn (fun m' : M => if h : m' ∈ (U : Set M) then
            (e (H (e.symm ⟨m', h⟩)) : M) else m') (U : Set M) := by
          rw [continuousOn_iff_continuous_domRestrict]
          have h2 : Continuous (fun m' : (U : Set M) => (e (H (e.symm m')) : M)) :=
            continuous_subtype_val.comp (e.continuous.comp (hH.comp e.symm.continuous))
          refine h2.congr fun m' => ?_
          simp only [Set.domRestrict_apply, dif_pos m'.2, Subtype.coe_eta]
        exact hc.continuousAt (U.isOpen.mem_nhds hU)
      apply hloc.congr_of_eventuallyEq
      filter_upwards [U.isOpen.mem_nhds hU] with m' hm'
      have h1 := hon (e.symm ⟨m', hm'⟩)
      rw [e.apply_symm_apply] at h1
      rw [dif_pos hm']
      exact h1
    · apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [hTc.isOpen_compl.mem_nhds hm] with m' hm'
      exact hoff m' hm'
  have hθfc : Continuous θf := hcont F hFc θf hθf_on hθf_off
  have hθic : Continuous θi := hcont Fi hFic θi hθi_on hθi_off
  have hleft : ∀ m, θi (θf m) = m := by
    intro m
    by_cases hU : m ∈ (U : Set M)
    · have hm : m = e (e.symm ⟨m, hU⟩) := by rw [e.apply_symm_apply]
      rw [hm, hθf_on, hθi_on, hFiF]
    · have h1 : θf m = m := by simp only [θf, dif_neg hU]
      rw [h1]
      simp only [θi, dif_neg hU]
  have hright : ∀ m, θf (θi m) = m := by
    intro m
    by_cases hU : m ∈ (U : Set M)
    · have hm : m = e (e.symm ⟨m, hU⟩) := by rw [e.apply_symm_apply]
      rw [hm, hθi_on, hθf_on, hFFi]
    · have h1 : θi m = m := by simp only [θi, dif_neg hU]
      rw [h1]
      simp only [θf, dif_neg hU]
  let θ : M ≃ₜ M :=
    { toFun := θf
      invFun := θi
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hθfc
      continuous_invFun := hθic }
  have hb : ∀ b : B, θ b.val = (G 1 b).val := by
    intro b
    have h0 : (0 : ℝ) ∈ _root_.Set.Ico (0 : ℝ) δ := ⟨le_rfl, hδ⟩
    have h1 := he0 b
    have h2 := he0 (G 1 b)
    change θf b.val = _
    have hbv : b.val = (e (b, ⟨0, h0⟩) : M) := h1.symm
    rw [hbv, hθf_on]
    have hF : F (b, ⟨0, h0⟩) = (G 1 b, ⟨0, h0⟩) := by
      refine Prod.ext ?_ rfl
      change G (φ 0) b = G 1 b
      rw [hφ0]
    rw [hF]
    exact h2
  refine ⟨θ, ?_, hb⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := hb ⟨x, hx⟩
    change θ x ∈ _
    rw [show x = (⟨x, hx⟩ : B).val from rfl, h]
    exact (G 1 ⟨x, hx⟩).2
  · intro hy
    obtain ⟨b, hb'⟩ := (G 1).surjective (⟨y, hy⟩ : B)
    refine ⟨b.val, b.2, ?_⟩
    rw [hb, hb']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_of_boundary_isotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_of_boundary_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_of_boundary_isotopy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_of_boundary_isotopy

end DifferentialGeometry.Topology.PiecewiseLinear
