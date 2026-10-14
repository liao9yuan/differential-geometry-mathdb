/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.BicollarNeighborhood
import Submission.DifferentialGeometry.Topology.OpenEmbeddingFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSurfaceComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]

theorem IsPolyhedralManifold.exists_twoSidedCollar {S U : Set X}
    (hS : IsPolyhedralManifold (n := 3) 2 S) (htwo : DifferentialGeometry.Topology.IsTwoSided S)
    (hU : U ∈ 𝓝ˢ S) :
    ∃ c : ThreeManifold.TwoSidedCollar (Subtype.val : S → X), Set.range c.toFun ⊆ U := by
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  obtain ⟨T, W, C, ρ, hWU, hWS, -, -, hcenter⟩ := hS.exists_bicollar htwo hU
  let f : S × _root_.Set.Icc (-1 : ℝ) 1 → X := Subtype.val ∘ ρ
  have hf : _root_.Topology.IsEmbedding f := IsEmbedding.subtypeVal.comp ρ.isEmbedding
  have hrange : Set.range f = W := by
    change Set.range (Subtype.val ∘ ρ) = W
    rw [Set.range_comp, ρ.surjective.range_eq, _root_.Set.image_univ, Subtype.range_coe]
  have hneighborhood : Set.range f ∈ 𝓝ˢ (Set.range (Subtype.val : S → X)) := by
    simpa only [hrange, Subtype.range_coe] using hWS
  obtain ⟨c, hc⟩ := exists_twoSidedCollar_of_closedInterval zero_lt_one f hf hcenter hneighborhood
  exact ⟨c, hc.trans (hrange.symm ▸ hWU)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_twoSidedCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_twoSidedCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_twoSidedCollar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_twoSidedCollar

theorem IsPolyhedralManifold.isBicollared {S : Set X}
    (hS : IsPolyhedralManifold (n := 3) 2 S)
    (htwo : DifferentialGeometry.Topology.IsTwoSided S) : IsBicollared S := by
  obtain ⟨c, -⟩ := hS.exists_twoSidedCollar htwo (U := _root_.Set.univ) Filter.univ_mem
  exact ⟨c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared

theorem IsPolyhedralManifold.isBicollared_image
    {Y : Type*} [TopologicalSpace Y] {S U : Set X}
    (hS : IsPolyhedralManifold (n := 3) 2 S)
    (htwo : DifferentialGeometry.Topology.IsTwoSided S) (hU : U ∈ 𝓝ˢ S)
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding (fun x : U => f x)) : IsBicollared (f '' S) := by
  obtain ⟨c, hc⟩ := hS.exists_twoSidedCollar htwo hU
  simpa only [Subtype.range_coe] using c.isBicollared_image hc hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isBicollared_image

theorem IsPLSphere.isBicollared_image
    {S U : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S)
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U) (hSU : S ⊆ U) :
    IsBicollared (f '' S) := by
  have hpoly : IsPolyhedralManifold (n := 3) 2 S := by
    have h := isPolyhedralSphere_chart_symm_image
      (chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3)))
      (chart_mem_atlas _ _) hS (by rw [chartAt_self_eq]; exact _root_.Set.subset_univ S)
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, _root_.Set.image_id] using h.isPolyhedralManifold
  have hneighborhood : U ∈ 𝓝ˢ S :=
    subset_interior_iff_mem_nhdsSet.mp (hU.interior_eq.symm ▸ hSU)
  apply hpoly.isBicollared_image (hpoly.isTwoSided hS.isConnected) hneighborhood
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hf.domRestrict
    (fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy))
  intro V hV
  change IsOpen ((f ∘ Subtype.val) '' V)
  rw [_root_.Set.image_comp]
  apply isOpen_image_of_subset_of_injOn hf hinj (hU.isOpenMap_subtype_val V hV)
  rintro _ ⟨x, _, rfl⟩
  exact x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared_image

theorem IsPLSphere.isBicollared {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) : IsBicollared S := by
  simpa only [_root_.Set.image_id] using hS.isBicollared_image isOpen_univ
    (f := id) continuous_id.continuousOn Function.injective_id.injOn (_root_.Set.subset_univ S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isBicollared

theorem IsPLBall.isBicollared_frontier_image
    {P U : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U) (hPU : P ⊆ U) :
    IsBicollared (frontier (f '' P)) := by
  rw [frontier_image_eq_image_frontier hU hf hinj hPU hP.isPolyhedron.isCompact]
  exact hP.isPLSphere_frontier.isBicollared_image hU hf hinj
    (hP.isPolyhedron.isCompact.isClosed.frontier_subset.trans hPU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier_image

theorem IsPLBall.isBicollared_frontier {P : Set (EuclideanSpace ℝ (Fin 3))}
    (hP : IsPLBall 3 P) : IsBicollared (frontier P) :=
  hP.isPLSphere_frontier.isBicollared

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isBicollared_frontier

end DifferentialGeometry.Topology.PiecewiseLinear
