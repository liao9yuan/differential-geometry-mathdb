/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.BoundarySphereDegree
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleDegreeOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "S1" => _root_.Metric.sphere (0 : Plane) 1

theorem isPLCirclePositive_unitSphere_iff_localDegree_eq_one
    {f : Plane → Plane} (h : IsolatingRadius f 0 1) (hb : _root_.Set.BijOn f S1 S1) :
    IsPLCirclePositive S1 f ↔ euclideanLocalDegree f 0 ⟨1, h⟩ = 1 := by
  let g : loopCircle → Plane := fun θ => planarCircleParam θ
  have hgc : Continuous g := continuous_subtype_val.comp planarCircleParam.continuous
  have hgb : _root_.Set.BijOn g _root_.Set.univ S1 := by
    refine ⟨fun θ _ => (planarCircleParam θ).2, ?_, ?_⟩
    · intro a _ b _ hab
      exact planarCircleParam.injective (Subtype.ext hab)
    · intro z hz
      refine ⟨planarCircleParam.symm ⟨z, hz⟩, _root_.Set.mem_univ _, ?_⟩
      exact congrArg Subtype.val (planarCircleParam.apply_symm_apply ⟨z, hz⟩)
  have hfc : ContinuousOn f S1 := h.continuousOn.mono _root_.Metric.sphere_subset_closedBall
  have heq : (circleSphereHomeomorph hgc hgb hfc hb).toHomotopyEquiv.toFun =
      h.boundarySphereMap hb.mapsTo := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    have hval := circleConj_spec hgb hb.mapsTo (planarCircleParam.symm z)
    change (planarCircleParam (circleConj g f (planarCircleParam.symm z)) : Plane) =
      f (planarCircleParam (planarCircleParam.symm z)) at hval
    rw [planarCircleParam.apply_symm_apply] at hval
    exact hval
  rw [isPLCirclePositive_iff_euclideanSphereDegree_eq_one hgc hgb hfc hb, heq,
    euclideanLocalDegree_eq_boundarySphereDegree h hb.mapsTo]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_unitSphere_iff_localDegree_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_unitSphere_iff_localDegree_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_unitSphere_iff_localDegree_eq_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_unitSphere_iff_localDegree_eq_one

end DifferentialGeometry.Topology.PiecewiseLinear
