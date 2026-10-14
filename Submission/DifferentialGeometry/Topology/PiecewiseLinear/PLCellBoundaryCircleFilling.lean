/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.exists_boundary_disk_disjoint_of_isPreconnected
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {V S Y J : Set M} (hV : IsPLCellOn 3 V S) (hY : IsPreconnected Y) (hYS : Y ⊆ S)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJS : J ⊆ S) (hYJ : Disjoint Y J) :
    ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ S ∧ Disjoint Y D := by
  obtain ⟨P, p, u, hp, hu, -, hSP⟩ := hV
  have hP : IsPLBall 3 P := ⟨p, hp⟩
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hp] at hSP
  let g := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hSuP : S ⊆ u '' P := by rw [hSP]; exact _root_.Set.image_mono hfrP
  have hright : ∀ y ∈ u '' P, u (g y) = y :=
    fun y hy => hu.injOn.bijOn_image.invOn_invFunOn.2 hy
  have hgfr : g '' S ⊆ frontier P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hSP.subset hy
    rw [← hzy, hleft (hfrP hz)]
    exact hz
  have hJmodel : IsPLSphere 1 (g '' J) :=
    hu.isPLSphere_invFunOn_image hJ (hJS.trans hSuP)
  have hYmodel : IsPreconnected (g '' Y) := hY.image g
    ((show ContinuousOn g (u '' P) from fun x hx =>
      (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn x hx).continuousWithinAt).mono
        (hYS.trans hSuP))
  have hdis : Disjoint (g '' Y) (g '' J) := by
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := by
      rw [← hright y (hSuP (hYS hy)), ← hright z (hSuP (hJS hz)), hyx, hzx]
    exact disjoint_left.mp hYJ hy (hyz.symm ▸ hz)
  obtain ⟨D, q, hq, hDfr, hYD, hqJ⟩ :=
    hP.isPLSphere_frontier.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
      hYmodel ((_root_.Set.image_mono hYS).trans hgfr) hJmodel ((_root_.Set.image_mono hJS).trans hgfr) hdis
  have hDP : D ⊆ P := hDfr.trans hfrP
  have hDpoly : IsPolyhedron D := (IsPLBall.isPolyhedron ⟨q, hq⟩)
  have himageJ : u '' (g '' J) = J := by
    rw [_root_.Set.image_image]
    calc
      (u ∘ g) '' J = id '' J := _root_.Set.image_congr fun y hy => hright y (hSuP (hJS hy))
      _ = J := _root_.Set.image_id _
  refine ⟨u '' D, ⟨D, q, u, hq, hu.mono_of_polyhedron hDpoly hDP, rfl, ?_⟩, ?_, ?_⟩
  · rw [hqJ, himageJ]
  · rw [hSP]
    exact _root_.Set.image_mono hDfr
  · apply disjoint_left.mpr
    rintro y hy ⟨z, hz, hzy⟩
    apply disjoint_left.mp hYD (show z ∈ g '' Y from ?_) hz
    exact ⟨y, hy, by rw [← hzy, hleft (hDP hz)]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_disjoint_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_disjoint_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_disjoint_of_isPreconnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_boundary_disk_disjoint_of_isPreconnected

end DifferentialGeometry.Topology.PiecewiseLinear
