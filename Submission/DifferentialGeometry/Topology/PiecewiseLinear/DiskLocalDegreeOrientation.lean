/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.CompactSupportOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleLocalDegreeOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "D" => _root_.Metric.closedBall (0 : Plane) 1
local notation "B" => _root_.Metric.ball (0 : Plane) 1
local notation "S1" => _root_.Metric.sphere (0 : Plane) 1

theorem isPLCirclePositive_iff_localDegree_sub_eq_one
    {f : Plane → Plane} (hf : ContinuousOn f D) (hinj : _root_.Set.InjOn f D)
    (hB : _root_.Set.MapsTo f B B) (hS : _root_.Set.BijOn f S1 S1) {x : Plane} (hx : x ∈ B) :
    IsPLCirclePositive S1 f ↔
      euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn _root_.Metric.isOpen_ball (hf.mono _root_.Metric.ball_subset_closedBall)
          (hinj.mono _root_.Metric.ball_subset_closedBall) hx) = 1 := by
  have h0 : (0 : Plane) ∈ B := _root_.Metric.mem_ball_self (by norm_num)
  obtain ⟨H, -, hfix, hmove⟩ := exists_isPLHomeomorphOn_map_point_eqOn_compl
    _root_.Metric.isOpen_ball (convex_ball (0 : Plane) 1).isPreconnected (hB h0) h0
  let F : Plane → Plane := H ∘ f
  have hF0 : F 0 = 0 := hmove
  have hR : IsolatingRadius F 0 1 := {
    pos := by norm_num
    continuousOn := H.continuous.comp_continuousOn hf
    zero_iff := fun z hz => by
      constructor
      · intro hz0
        exact hinj hz (_root_.Metric.mem_closedBall_self (by norm_num))
          (H.injective (hz0.trans hmove.symm))
      · intro hzero
        simpa only [hzero] using hF0 }
  have hEq : _root_.Set.EqOn F f S1 := by
    intro z hz
    change H (f z) = f z
    apply hfix
    have hs := hS.mapsTo hz
    rw [mem_sphere_zero_iff_norm] at hs
    rw [_root_.Set.mem_compl_iff, mem_ball_zero_iff, hs]
    exact lt_irrefl 1
  have hFS : _root_.Set.BijOn F S1 S1 := hS.congr hEq.symm
  have hFixD : _root_.Set.EqOn H id Dᶜ :=
    hfix.mono (compl_subset_compl.mpr _root_.Metric.ball_subset_closedBall)
  have hHdeg := euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact
    H.continuous H.injective (_root_.ProperSpace.isCompact_closedBall 0 1) hFixD (f 0)
  have hcomp := euclideanLocalDegree_sub_comp_of_injOn _root_.Metric.isOpen_ball isOpen_univ
    (hf.mono _root_.Metric.ball_subset_closedBall) (hinj.mono _root_.Metric.ball_subset_closedBall)
    H.continuous.continuousOn H.injective.injOn (_root_.Set.mapsTo_univ f B) h0
  rw [hHdeg, mul_one] at hcomp
  have hFdeg : euclideanLocalDegree F 0 ⟨1, hR⟩ =
      euclideanLocalDegree (fun z => f z - f 0) 0
        (isolatedZero_sub_of_injOn _root_.Metric.isOpen_ball (hf.mono _root_.Metric.ball_subset_closedBall)
          (hinj.mono _root_.Metric.ball_subset_closedBall) h0) := by
    simpa only [F, Function.comp_def, hmove, sub_zero] using hcomp
  have hconst := euclideanLocalDegree_sub_eq_of_injOn _root_.Metric.isOpen_ball
    (convex_ball (0 : Plane) 1).isPreconnected
    (hf.mono _root_.Metric.ball_subset_closedBall) (hinj.mono _root_.Metric.ball_subset_closedBall) h0 hx
  have hpos : IsPLCirclePositive S1 f ↔ IsPLCirclePositive S1 F :=
    ⟨fun h => h.of_eqOn hEq, fun h => h.of_eqOn hEq.symm⟩
  rw [hpos, isPLCirclePositive_unitSphere_iff_localDegree_eq_one hR hFS, hFdeg, hconst]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_iff_localDegree_sub_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_iff_localDegree_sub_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_iff_localDegree_sub_eq_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_iff_localDegree_sub_eq_one

end DifferentialGeometry.Topology.PiecewiseLinear
