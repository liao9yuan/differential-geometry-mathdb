/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCellProperness
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsPLHalfSpacePairAt {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (W H : Set M) (z : M) : Prop :=
  ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
    e ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ z ∈ e.source ∧
      (∀ y ∈ e.source, y ∈ W ↔ 0 ≤ ℓ (e y)) ∧
      ∀ y ∈ e.source, y ∈ H ↔ ℓ (e y) = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHalfSpacePairAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHalfSpacePairAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHalfSpacePairAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHalfSpacePairAt

def IsPLBoundarySide {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (W BdM : Set M) : Prop :=
  D '' D.domain ⊆ W ∧
    IsClosed W ∧
    IsClosed BdM ∧
    D '' (D.domain \ frontier D.domain) ⊆ interior W ∧
    ∀ z ∈ D '' frontier D.domain, IsPLHalfSpacePairAt W BdM z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide

theorem IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {W BdM : Set M} (hside : IsPLBoundarySide D W BdM)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain) :
    D '' (D.domain \ frontier D.domain) ⊆ interior (W \ BdM) := by
  obtain ⟨-, -, hBd, hint, -⟩ := hside
  have hsub : interior W ∩ BdMᶜ ⊆ interior (W \ BdM) := by
    rw [Set.sdiff_eq, interior_inter, hBd.isOpen_compl.interior_eq]
  rintro _ ⟨x, hx, rfl⟩
  refine hsub ⟨hint ⟨x, hx, rfl⟩, fun hmem => hx.2 ?_⟩
  rw [← hproper]
  exact ⟨hx.1, hmem⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff

def IsPLBoundaryTubeProducer (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  ∀ (D : SingularTwoCell M) (BdM B W : Set M)
    (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
    IsPLBoundarySide D W BdM →
    (∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) →
    ∃ (U : Set M) (T : CrossSeamTubeData hD c U),
      Nonempty (PLSeamTubeChart M T.chart) ∧
        T.chart '' spliceCylinder ⊆ W ∧
        T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks ∧
        ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundaryTubeProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundaryTubeProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundaryTubeProducer ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBoundaryTubeProducer

open _root_.Classical in
theorem isPLBoundarySide_double
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (boundaryComplex 3 K).space)
    ∀ {D : SingularTwoCell (double 3 K).space},
      _root_.Set.MapsTo D D.domain C →
      D.domain ∩ D ⁻¹' Bd = frontier D.domain →
      IsPLBoundarySide D C Bd := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
    (ι '' (boundaryComplex 3 K).space)
  change ∀ {D : SingularTwoCell (double 3 K).space},
    _root_.Set.MapsTo D D.domain C →
    D.domain ∩ D ⁻¹' Bd = frontier D.domain →
    IsPLBoundarySide D C Bd
  intro D hmap hproper
  obtain ⟨x₀, hx₀⟩ := D.isPLBall_domain.nonempty
  have hDx₀ := hmap hx₀
  change (D x₀ : E × E × ℝ) ∈ ι '' K.space at hDx₀
  obtain ⟨y₀, hy₀, -⟩ := hDx₀
  let p : K.space := ⟨y₀, hy₀⟩
  have hC : C = ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (glued₂ K (boundaryComplex 3 K) id).space := by
    rw [glued₂_space]
  let _ : Finite (glued₂ K (boundaryComplex 3 K) id).faces :=
    (glued₂_faces_finite K (boundaryComplex 3 K) id).to_subtype
  have hclosed : IsClosed C := by
    rw [hC]
    exact (isPolyhedron_space (glued₂ K (boundaryComplex 3 K) id)).isClosed.preimage
      continuous_subtype_val
  have hfront : frontier C = Bd := by
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K hK
  have hinterior : interior C = C \ Bd := by
    rw [← self_sdiff_frontier C, hfront]
  have hBdclosed : IsClosed Bd := by
    rw [← hfront]
    exact isClosed_frontier
  refine ⟨image_subset_iff.mpr hmap, hclosed, hBdclosed, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hinterior]
    refine ⟨hmap hx.1, ?_⟩
    intro hyBd
    have hxfront : x ∈ frontier D.domain := by
      rw [← hproper]
      exact ⟨hx.1, hyBd⟩
    exact hx.2 hxfront
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hyBd : D x ∈ Bd := by
      have hpair : x ∈ D.domain ∩ D ⁻¹' Bd := by
        rw [hproper]
        exact hx
      exact hpair.2
    have hyfront : D x ∈ frontier C := by
      rw [hfront]
      exact hyBd
    obtain ⟨e, ℓ, he, hℓ, hye, hCmem, hBdmem⟩ :=
      exists_halfSpace_chart_glued₂_space_in_double K hK p (D x) hyfront
    refine ⟨e, ℓ, he, hℓ, hye, ?_, ?_⟩
    · exact hCmem
    · intro z hz
      have hBdmem' := hBdmem z hz
      change z ∈ frontier C ↔ ℓ (e z) = 0 at hBdmem'
      rw [hfront] at hBdmem'
      exact hBdmem'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double

open _root_.Classical in
theorem isPLBoundarySide_double_of_normal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (boundaryComplex 3 K).space)
    ∀ {D : SingularTwoCell (double 3 K).space} {B : Set (double 3 K).space},
      NormalSingularCellData D Bd B → _root_.Set.MapsTo D D.domain C →
      IsPLBoundarySide D C Bd := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
    (ι '' (boundaryComplex 3 K).space)
  change ∀ {D : SingularTwoCell (double 3 K).space} {B : Set (double 3 K).space},
    NormalSingularCellData D Bd B → _root_.Set.MapsTo D D.domain C →
    IsPLBoundarySide D C Bd
  intro D B hD hmap
  apply isPLBoundarySide_double K hK hmap
  simpa only using hD.preimage_boundary_eq_frontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double_of_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double_of_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double_of_normal ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundarySide_double_of_normal

end DifferentialGeometry.Topology.PiecewiseLinear
