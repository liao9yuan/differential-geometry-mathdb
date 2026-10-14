/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLAt_of_mem_maximalAtlas {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ (plGroupoid n).maximalAtlas M) {y : M} (hy : y ∈ c.source) :
    IsPLAt n n c y := by
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) c _root_.Set.univ y
  rw [StructureGroupoid.liftPropWithinAt_self_target]
  refine ⟨(c.continuousAt hy).continuousWithinAt, ?_⟩
  have hye : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source := mem_chart_source _ y
  have hT : (chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c ∈ plGroupoid n :=
    StructureGroupoid.compatible_of_mem_maximalAtlas_right hc
  have hyT : chartAt (EuclideanSpace ℝ (Fin n)) y y ∈
      ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    refine ⟨(chartAt (EuclideanSpace ℝ (Fin n)) y).map_source hye, ?_⟩
    change (chartAt (EuclideanSpace ℝ (Fin n)) y).symm (chartAt (EuclideanSpace ℝ (Fin n)) y y) ∈
      c.source
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) y).left_inv hye]
    exact hy
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := (mem_plGroupoid_iff.mp hT).1 _ hyT
  rw [_root_.Set.preimage_univ]
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, _root_.Set.subset_univ _, (hC i).2.2⟩, ?_⟩
  rw [nhdsWithin_univ]
  rwa [((chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c).open_source.nhdsWithin_eq hyT] at hCx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLAt_of_mem_maximalAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLAt_of_mem_maximalAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLAt_of_mem_maximalAtlas ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLAt_of_mem_maximalAtlas

theorem IsPLCellOn.exists_isPLHomeomorphOn_image_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source) :
    ∃ q : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin (d + 1))) (c '' S) ∧
        c '' B = q '' stdSimplexBoundary d := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hS
  have hP : IsPolyhedron P := IsPLBall.isPolyhedron ⟨r, hr⟩
  have hcu : IsPLOn 3 3 (c ∘ u) P := fun x hx =>
    IsPLAt.comp_isPLWithinAt (isPLAt_of_mem_maximalAtlas hc (hSc ⟨x, hx, rfl⟩))
      (hu.isPLOn x hx)
  have hpa : IsPiecewiseAffineOn (c ∘ u) P := isPLOn_iff_isPiecewiseAffineOn.mp hcu
  have hinj : _root_.Set.InjOn (c ∘ u) P := fun x hx y hy hxy =>
    hu.injOn hx hy (c.injOn (hSc ⟨x, hx, rfl⟩) (hSc ⟨y, hy, rfl⟩) hxy)
  have h := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hpa hinj.bijOn_image
  refine ⟨(c ∘ u) ∘ r, ?_, ?_⟩
  · rw [← _root_.Set.image_comp]
    exact hr.trans h
  · rw [_root_.Set.image_comp, _root_.Set.image_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isPLHomeomorphOn_image_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isPLHomeomorphOn_image_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isPLHomeomorphOn_image_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isPLHomeomorphOn_image_chart

theorem IsPLCellOn.isPLBall_image_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M} (hS : IsPLCellOn 3 S B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source) :
    IsPLBall 3 (c '' S) ∧ c '' B = frontier (c '' S) := by
  obtain ⟨q, hq, hB⟩ := hS.exists_isPLHomeomorphOn_image_chart hc hSc
  exact ⟨⟨q, hq⟩, hB.trans (IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hq)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPLBall_image_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPLBall_image_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPLBall_image_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPLBall_image_chart

end DifferentialGeometry.Topology.PiecewiseLinear
