/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsHPolytope (C : Set E) : Prop :=
  IsCompact C ∧ ∃ (ι : Type) (_ : Finite ι) (l : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ),
    C = {x | ∀ i, l i x ≤ c i}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope

namespace IsHPolytope

variable {C D : Set E}

theorem isCompact (hC : IsHPolytope C) : IsCompact C := hC.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isCompact

theorem isClosed (hC : IsHPolytope C) : IsClosed C := hC.1.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isClosed

theorem convex (hC : IsHPolytope C) : Convex ℝ C := by
  obtain ⟨_, ι, _, l, c, rfl⟩ := hC
  intro x hx y hy a b ha hb hab i
  rw [map_add, map_smul, map_smul]
  change a * l i x + b * l i y ≤ c i
  calc
    a * l i x + b * l i y ≤ a * c i + b * c i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = c i := by rw [← add_mul, hab, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.convex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.convex

theorem univ_of_subsingleton [Subsingleton E] : IsHPolytope (_root_.Set.univ : Set E) :=
  ⟨isCompact_univ, Empty, inferInstance, fun i => i.elim, fun i => i.elim, by
    ext x
    simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.univ_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.univ_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.univ_of_subsingleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.univ_of_subsingleton

theorem inter (hC : IsHPolytope C) (hD : IsHPolytope D) : IsHPolytope (C ∩ D) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  obtain ⟨hDc, κ, hκ, m, d, rfl⟩ := hD
  have := hι
  have := hκ
  refine ⟨hCc.inter_right hDc.isClosed, ι ⊕ κ, inferInstance, Sum.elim l m, Sum.elim c d, ?_⟩
  ext x
  simp [Sum.forall]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter

theorem inter_preimage [FiniteDimensional ℝ E] (hC : IsHPolytope C) {D : Set F}
    (hD : IsHPolytope D) (A : E →ᵃ[ℝ] F) : IsHPolytope (C ∩ A ⁻¹' D) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  obtain ⟨hDc, κ, hκ, m, d, rfl⟩ := hD
  have := hι
  have := hκ
  have hA : ∀ y, A y = A.linear y + A 0 := fun y => by simpa using A.map_vadd 0 y
  refine ⟨hCc.inter_right (hDc.isClosed.preimage A.continuous_of_finiteDimensional),
    ι ⊕ κ, inferInstance, Sum.elim l fun j => (m j).comp A.linear,
    Sum.elim c fun j => d j - m j (A 0), ?_⟩
  ext x
  simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    LinearMap.comp_apply]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [hA x, map_add]
  constructor <;> intro h <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter_preimage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.inter_preimage

theorem image_affineEquiv [FiniteDimensional ℝ E] (hC : IsHPolytope C) (T : E ≃ᵃ[ℝ] F) :
    IsHPolytope (T '' C) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  have := hι
  have hT : Continuous T := by simpa using T.toAffineMap.continuous_of_finiteDimensional
  have hS : ∀ y, T.symm y = T.symm.linear y + T.symm 0 := fun y => by
    simpa using T.symm.map_vadd 0 y
  refine ⟨hCc.image hT, ι, inferInstance, fun i => (l i).comp (T.symm.linear : F →ₗ[ℝ] E),
    fun i => c i - l i (T.symm 0), ?_⟩
  ext y
  simp only [_root_.Set.mem_image, _root_.Set.mem_ofPred_eq, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hx' := hx i
    have h1 : T.symm.linear (T x) = x - T.symm 0 := by
      have h := hS (T x)
      rw [T.symm_apply_apply] at h
      exact eq_sub_of_add_eq h.symm
    rw [h1, map_sub]
    linarith
  · intro hy
    refine ⟨T.symm y, fun i => ?_, T.apply_symm_apply y⟩
    have h := hy i
    rw [hS y, map_add]
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.image_affineEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.image_affineEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.image_affineEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.image_affineEquiv

end IsHPolytope

theorem exists_isHPolytope_subset_mem_nhds [FiniteDimensional ℝ E] {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) : ∃ C : Set E, IsHPolytope C ∧ C ⊆ U ∧ C ∈ 𝓝 x := by
  let L := (Module.finBasis ℝ E).equivFunL
  have hpre : L.symm ⁻¹' U ∈ 𝓝 (L x) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨L ⁻¹' Metric.closedBall (L x) (r / 2), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← L.image_symm_eq_preimage]
    exact (_root_.ProperSpace.isCompact_closedBall _ _).image L.symm.continuous
  · let Lℓ : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := L.toLinearEquiv
    refine ⟨Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E), inferInstance,
      Sum.elim (fun i => (LinearMap.proj i).comp Lℓ) (fun i => -((LinearMap.proj i).comp Lℓ)),
      Sum.elim (fun i => L x i + r / 2) (fun i => r / 2 - L x i), ?_⟩
    ext y
    simp only [_root_.Set.mem_preimage, Metric.mem_closedBall, _root_.Set.mem_ofPred_eq, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.neg_apply, Lℓ,
      LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [dist_pi_le_iff (by positivity)]
    simp only [Real.dist_eq, abs_le]
    constructor
    · intro h
      exact ⟨fun i => by linarith [(h i).2], fun i => by linarith [(h i).1]⟩
    · rintro ⟨h1, h2⟩ i
      exact ⟨by linarith [h2 i], by linarith [h1 i]⟩
  · intro y hy
    have hy' : L y ∈ Metric.ball (L x) r := Metric.closedBall_subset_ball (by linarith) hy
    simpa using hball hy'
  · exact L.continuous.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isHPolytope_subset_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isHPolytope_subset_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isHPolytope_subset_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isHPolytope_subset_mem_nhds

end DifferentialGeometry.Topology.PiecewiseLinear
