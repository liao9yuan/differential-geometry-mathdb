/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Embedding.SubtypeRestriction
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.Function _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

structure SmoothBoundaryAtlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ) [NeZero n] (K : Set M) where
  ambientChart : K → PartialDiffeomorph I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    M (EuclideanSpace ℝ (Fin n)) ∞
  mem_source : ∀ x : K, x.val ∈ (ambientChart x).source
  mem_iff : ∀ x : K, ∀ y ∈ (ambientChart x).source, y ∈ K ↔ 0 ≤ ambientChart x y 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas

namespace SmoothBoundaryAtlas

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

def chart (x : K) : _root_.OpenPartialHomeomorph K (EuclideanHalfSpace n) :=
  OpenPartialHomeomorph.restrictSubtypes (C.ambientChart x).toOpenPartialHomeomorph
    K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x (0 : EuclideanHalfSpace n) (C.mem_iff x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.chart ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.chart

@[reducible]
def toChartedSpace : ChartedSpace (EuclideanHalfSpace n) K where
  atlas := _root_.Set.range C.chart
  chartAt := C.chart
  mem_chart_source := C.mem_source
  chart_mem_atlas := fun x ↦ _root_.Set.mem_range_self x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.toChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.toChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.toChartedSpace ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.toChartedSpace

private theorem change_mem_source (x y : K) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
        ((C.chart x).symm.trans (C.chart y)).source ∩
        _root_.Set.range (modelWithCornersEuclideanHalfSpace n)) :
    z ∈ ((C.ambientChart x).symm.trans (C.ambientChart y)).source := by
  let ih := modelWithCornersEuclideanHalfSpace n
  have hval : (ih.symm z).val = z := ih.right_inv hz.2
  have htarget : z ∈ (C.ambientChart x).target := by
    have h := hz.1.1
    change (ih.symm z).val ∈ (C.ambientChart x).target at h
    rwa [hval] at h
  have hinv : ((C.chart x).symm (ih.symm z) : M) = (C.ambientChart x).symm z := by
    rw [chart, OpenPartialHomeomorph.restrictSubtypes_symm_apply]
    · rw [hval]; rfl
    · change (ih.symm z).val ∈ (C.ambientChart x).target
      rwa [hval]
  refine ⟨htarget, ?_⟩
  have h := hz.1.2
  change ((C.chart x).symm (ih.symm z) : M) ∈ (C.ambientChart y).source at h
  rwa [hinv] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.change_mem_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothBoundaryAtlas.change_mem_source target :: scope.openDecls } }

private theorem change_eq (x y : K) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
        ((C.chart x).symm.trans (C.chart y)).source ∩
        _root_.Set.range (modelWithCornersEuclideanHalfSpace n)) :
    modelWithCornersEuclideanHalfSpace n
        (((C.chart x).symm.trans (C.chart y)) ((modelWithCornersEuclideanHalfSpace n).symm z)) =
      ((C.ambientChart x).symm.trans (C.ambientChart y)) z := by
  let ih := modelWithCornersEuclideanHalfSpace n
  have hval : (ih.symm z).val = z := ih.right_inv hz.2
  change ((C.chart y) ((C.chart x).symm (ih.symm z))).val = _
  rw [show ((C.chart y) ((C.chart x).symm (ih.symm z))).val =
      (C.ambientChart y) ((C.chart x).symm (ih.symm z)) from
    OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hz.1.2]
  have hinv := OpenPartialHomeomorph.restrictSubtypes_symm_apply
    (C.ambientChart x).toOpenPartialHomeomorph K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x (0 : EuclideanHalfSpace n) (C.mem_iff x) (ih.symm z) hz.1.1
  change ((C.chart x).symm (ih.symm z) : M) = (C.ambientChart x).symm (ih.symm z).val at hinv
  rw [hinv, hval]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.change_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothBoundaryAtlas.change_eq target :: scope.openDecls } }

theorem isManifold :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanHalfSpace n) _
      (modelWithCornersEuclideanHalfSpace n) ∞ K _ C.toChartedSpace := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  apply isManifold_of_contDiffOn (modelWithCornersEuclideanHalfSpace n) ∞ K
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  have hc := ((C.ambientChart x).symm.trans (C.ambientChart y)).contMDiffOn_toFun.contDiffOn
  exact (hc.mono (C.change_mem_source x y)).congr (C.change_eq x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isManifold ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.isManifold

theorem isBoundaryPoint_iff (x : K) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (EuclideanSpace ℝ (Fin n)) _ _
      (EuclideanHalfSpace n) _ (modelWithCornersEuclideanHalfSpace n)
      K _ C.toChartedSpace x ↔ C.ambientChart x x.val 0 = 0 := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change (0 = (C.chart x x).val 0) ↔ _
  rw [chart, OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (C.mem_source x)]
  exact eq_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isBoundaryPoint_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.isBoundaryPoint_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isBoundaryPoint_iff ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.isBoundaryPoint_iff

theorem contMDiff_subtype_val :
    letI := C.toChartedSpace
    ContMDiff (modelWithCornersEuclideanHalfSpace n) I ∞ (Subtype.val : K → M) := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  let : IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ K := C.isManifold
  intro x
  have hext : extChartAt (modelWithCornersEuclideanHalfSpace n) x x =
      C.ambientChart x x.val := by
    change (C.chart x x).val = _
    exact OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (C.mem_source x)
  have hinv := (C.ambientChart x).contMDiffOn_invFun.contMDiffAt
    ((C.ambientChart x).open_target.mem_nhds
      ((C.ambientChart x).toPartialEquiv.map_source (C.mem_source x)))
  rw [← hext] at hinv
  have hcomp := hinv.comp x (contMDiffAt_extChartAt (I := modelWithCornersEuclideanHalfSpace n)
    (n := ∞) (x := x))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(C.chart x).open_source.mem_nhds (C.mem_source x)] with y hy
  change y.val = (C.ambientChart x).symm (C.chart x y).val
  rw [chart, OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy]
  exact ((C.ambientChart x).toPartialEquiv.left_inv hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_subtype_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_subtype_val

end SmoothBoundaryAtlas

end DifferentialGeometry.Topology
