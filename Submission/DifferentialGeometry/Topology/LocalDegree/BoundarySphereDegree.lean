/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

def IsolatingRadius.boundarySphereMap {f : E → E} (h : IsolatingRadius f 0 1)
    (hm : _root_.Set.MapsTo f (_root_.Metric.sphere 0 1) (_root_.Metric.sphere 0 1)) : C(EuclideanSphere d, EuclideanSphere d) :=
  ⟨fun z => ⟨f z, hm z.2⟩,
    ((h.continuousOn.mono _root_.Metric.sphere_subset_closedBall).domRestrict).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.boundarySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.boundarySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.boundarySphereMap ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.boundarySphereMap

theorem euclideanLocalDegree_eq_boundarySphereDegree {f : E → E}
    (h : IsolatingRadius f 0 1) (hm : _root_.Set.MapsTo f (_root_.Metric.sphere 0 1) (_root_.Metric.sphere 0 1)) :
    euclideanLocalDegree f 0 ⟨1, h⟩ = euclideanSphereDegree (h.boundarySphereMap hm) := by
  erw [euclideanLocalDegree_eq_sphereDegree _ h ⟨1, by norm_num, le_rfl⟩]
  congr 1
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rw [sphereMap_apply, zero_add, one_smul]
  change ‖f z‖⁻¹ • f z = f z
  rw [mem_sphere_zero_iff_norm.mp (hm z.2), inv_one, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_boundarySphereDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_boundarySphereDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_boundarySphereDegree ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_boundarySphereDegree

end DifferentialGeometry.LocalDegree
