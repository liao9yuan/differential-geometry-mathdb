/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

theorem subsingleton_integralFirstHomology_complement_point
    (p : EuclideanSpace ℝ (Fin 3)) :
    Subsingleton
      (integralSingularHomology 1
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  let e : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    (Homeomorph.subRight p).subtype (fun y => by
      change y ≠ p ↔ y - p ≠ 0
      exact sub_ne_zero.symm)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1 := by simp
  let _ : Subsingleton
      (integralSingularHomology 1
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    integralSphereHomology_subsingleton 2 1 _ hdim one_ne_zero (by norm_num)
  exact ((integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).trans
    (integralPuncturedSpaceSphereHomologyEquiv
      (EuclideanSpace ℝ (Fin 3)) 1)).toEquiv.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralFirstHomology_complement_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralFirstHomology_complement_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralFirstHomology_complement_point ``Submission.DifferentialGeometry.Topology.subsingleton_integralFirstHomology_complement_point

end DifferentialGeometry.Topology
