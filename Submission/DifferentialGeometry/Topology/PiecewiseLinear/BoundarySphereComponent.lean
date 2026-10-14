/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Submission.DifferentialGeometry.Topology.Simplex.NormedBall
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron
import Submission.DifferentialGeometry.Geometry.Boundary.Manifold.Basic
import Submission.DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem nonempty_homeomorph_stdSimplexBoundary_three_sphere :
    Nonempty ({z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hset : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} =
      DifferentialGeometry.Simplex.boundary (Fin (3 + 1)) := by
    ext z
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  exact ⟨(Homeomorph.setCongr hset).trans
    (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_homeomorph_stdSimplexBoundary_three_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.nonempty_homeomorph_stdSimplexBoundary_three_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_homeomorph_stdSimplexBoundary_three_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.nonempty_homeomorph_stdSimplexBoundary_three_sphere

theorem isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (ψ : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : _root_.Topology.IsClosedEmbedding ψ) (hψbd : _root_.Set.range ψ ⊆ (𝓡∂ 3).boundary M) :
    IsClopen ((fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' _root_.Set.range ψ) := by
  classical
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  obtain ⟨a₀⟩ := nonempty_homeomorph_stdSimplexBoundary_three_sphere
  let ψ' : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} →
      BoundaryManifold (𝓡∂ 3) M := fun z => ⟨ψ z, hψbd (_root_.Set.mem_range_self z)⟩
  have hψ'c : Continuous ψ' := hψ.continuous.subtype_mk _
  have hψ'i : Function.Injective ψ' := fun z w h => hψ.injective (congrArg Subtype.val h)
  have hpre : (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' _root_.Set.range ψ = _root_.Set.range ψ' := by
    ext b
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  refine ⟨hψ.isClosed_range.preimage continuous_subtype_val, ?_⟩
  rw [hpre, isOpen_iff_forall_mem_open]
  rintro _ ⟨z, rfl⟩
  let σ := chartAt (EuclideanSpace ℝ (Fin 2)) (a₀ z)
  let f : σ.target → BoundaryManifold (𝓡∂ 3) M := fun u => ψ' (a₀.symm (σ.symm u))
  have hfc : Continuous f := hψ'c.comp (a₀.symm.continuous.comp
    (σ.continuousOn_symm.comp_continuous continuous_subtype_val fun u => u.2))
  have hfi : Function.Injective f := fun u v h =>
    Subtype.ext (σ.symm.injOn u.2 v.2 (a₀.symm.injective (hψ'i h)))
  refine ⟨range f, ?_, isOpen_range_of_isOpen_of_continuous_injective_real (𝓡 2)
    σ.open_target f hfc hfi, ⟨σ (a₀ z), σ.map_source (mem_chart_source _ _)⟩, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact _root_.Set.mem_range_self _
  · change ψ' (a₀.symm (σ.symm (σ (a₀ z)))) = ψ' z
    rw [σ.left_inv (mem_chart_source _ _), Homeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding

theorem exists_opens_boundaryManifold_homeomorph_sphere
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (ψ : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : _root_.Topology.IsClosedEmbedding ψ) (hψbd : _root_.Set.range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ W : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M),
      IsClosed (W : Set (BoundaryManifold (𝓡∂ 3) M)) ∧ CompactSpace W ∧
      (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) '' W = _root_.Set.range ψ ∧
      Nonempty (W ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  classical
  have hcl := isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding ψ hψ hψbd
  obtain ⟨a₀⟩ := nonempty_homeomorph_stdSimplexBoundary_three_sphere
  let ψ' : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} →
      BoundaryManifold (𝓡∂ 3) M := fun z => ⟨ψ z, hψbd (_root_.Set.mem_range_self z)⟩
  have hψ'e : _root_.Topology.IsEmbedding ψ' := IsEmbedding.subtypeVal.of_comp_iff.mp hψ.isEmbedding
  have hpre : (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' _root_.Set.range ψ = _root_.Set.range ψ' := by
    ext b
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  let W : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M) := ⟨_, hcl.isOpen⟩
  let hW : W ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ((Homeomorph.setCongr hpre).trans hψ'e.toHomeomorph.symm).trans a₀
  refine ⟨W, hcl.isClosed, hW.symm.compactSpace, ?_, ⟨hW⟩⟩
  change (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ''
    ((fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' _root_.Set.range ψ) = _root_.Set.range ψ
  rw [_root_.Set.image_preimage_eq_inter_range, _root_.Set.inter_eq_left]
  rintro _ ⟨z, rfl⟩
  exact ⟨ψ' z, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_opens_boundaryManifold_homeomorph_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_opens_boundaryManifold_homeomorph_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_opens_boundaryManifold_homeomorph_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_opens_boundaryManifold_homeomorph_sphere

end DifferentialGeometry.Topology.PiecewiseLinear
