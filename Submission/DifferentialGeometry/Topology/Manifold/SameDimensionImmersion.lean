/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology

theorem continuousLinearEquiv_prod_self_complement_subsingleton
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (E × F) ≃L[ℝ] E) : Subsingleton F := by
  let i : F →ₗ[ℝ] E := e.toLinearMap.comp (LinearMap.inr ℝ E F)
  have hi : Function.Injective i := e.injective.comp LinearMap.inr_injective
  let _ : FiniteDimensional ℝ F := FiniteDimensional.of_injective i hi
  have hdim : Module.finrank ℝ (E × F) = Module.finrank ℝ E :=
    e.toLinearEquiv.finrank_eq
  have hzero : Module.finrank ℝ F = 0 := by
    rw [Module.finrank_prod] at hdim
    omega
  exact Module.finrank_zero_iff.mp hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuousLinearEquiv_prod_self_complement_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuousLinearEquiv_prod_self_complement_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuousLinearEquiv_prod_self_complement_subsingleton ``Submission.DifferentialGeometry.Topology.continuousLinearEquiv_prod_self_complement_subsingleton

theorem isLocalHomeomorph_of_isImmersion_modelSelf
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type w} {N : Type x} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace E N]
    {n : ℕ∞ω} {f : M → N}
    (hf : _root_.Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, E) n f) : IsLocalHomeomorph f := by
  apply IsLocalHomeomorph.mk f
  intro p
  let h := hf.isImmersionAt p
  let F := h.complement
  let eEF := h.equiv
  let _ : Subsingleton F := continuousLinearEquiv_prod_self_complement_subsingleton eEF
  let _ : Unique F :=
    { default := 0
      uniq := fun y => Subsingleton.elim y 0 }
  let e : E ≃L[ℝ] E := (ContinuousLinearEquiv.prodUnique ℝ E F).symm.trans eEF
  let phi : OpenPartialHomeomorph M N :=
    (h.domChart.trans e.toHomeomorph.toOpenPartialHomeomorph).trans h.codChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change p ∈ ((h.domChart.trans e.toHomeomorph.toOpenPartialHomeomorph).trans
        h.codChart.symm).source
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
    refine ⟨⟨h.mem_domChart_source, trivial⟩, ?_⟩
    change e (h.domChart p) ∈ h.codChart.target
    have hz : h.domChart p ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
      simpa [OpenPartialHomeomorph.extend_target] using
        h.domChart.map_source h.mem_domChart_source
    have hpcoord := h.writtenInCharts hz
    have hfp := h.mem_codChart_source
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_eq] at hpcoord
    rw [h.domChart.left_inv h.mem_domChart_source] at hpcoord
    change h.codChart (f p) = e (h.domChart p) at hpcoord
    rw [← hpcoord]
    exact h.codChart.map_source hfp
  · intro q hq
    change f q = h.codChart.symm (e (h.domChart q))
    have hqdom : q ∈ h.domChart.source := hq.1.1
    have hz : h.domChart q ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
      simpa [OpenPartialHomeomorph.extend_target] using h.domChart.map_source hqdom
    have hqcoord := h.writtenInCharts hz
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_eq] at hqcoord
    rw [h.domChart.left_inv hqdom] at hqcoord
    change h.codChart (f q) = e (h.domChart q) at hqcoord
    rw [← hqcoord]
    exact (h.codChart.left_inv (h.source_subset_preimage_source hqdom)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalHomeomorph_of_isImmersion_modelSelf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalHomeomorph_of_isImmersion_modelSelf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalHomeomorph_of_isImmersion_modelSelf ``Submission.DifferentialGeometry.Topology.isLocalHomeomorph_of_isImmersion_modelSelf

end DifferentialGeometry.Topology
