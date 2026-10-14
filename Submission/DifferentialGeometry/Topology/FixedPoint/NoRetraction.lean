/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import Mathlib.Topology.Connected.TotallyDisconnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric _root_.Module

namespace DifferentialGeometry.Topology.FixedPoint

theorem not_exists_retraction_closedBall_sphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 0 < _root_.Module.finrank ℝ E) :
    ¬ ∃ r : _root_.Metric.closedBall (0 : E) 1 → _root_.Metric.sphere (0 : E) 1,
      Continuous r ∧ ∀ x : _root_.Metric.sphere (0 : E) 1,
        r ⟨x.1, _root_.Metric.sphere_subset_closedBall x.2⟩ = x := by
  rintro ⟨r, hr, hret⟩
  let : ContractibleSpace (_root_.Metric.closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) 1).contractibleSpace ⟨0, by simp⟩
  let i : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.closedBall (0 : E) 1) :=
    ⟨fun x ↦ ⟨x.1, _root_.Metric.sphere_subset_closedBall x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  by_cases hdim : _root_.Module.finrank ℝ E = 1
  · let v := unitSpherePointOfFinrankPos (E := E) hd
    let := oneDimUnitSphere_finite hdim v
    have h := TotallyDisconnectedSpace.eq_of_continuous r hr (i v) (i (-v))
    dsimp only [i, ContinuousMap.coe_mk] at h
    rw [hret v, hret (-v)] at h
    exact unitSphere_ne_antipode v h
  · let n := _root_.Module.finrank ℝ E - 2
    have hn : _root_.Module.finrank ℝ E = n + 2 := by omega
    let := integralSingularHomology_subsingleton_of_contractible (n + 1)
      (by omega) (_root_.Metric.closedBall (0 : E) 1)
    let p : C(_root_.Metric.closedBall (0 : E) 1, _root_.Metric.sphere (0 : E) 1) := ⟨r, hr⟩
    have hcomp : p.comp i = ContinuousMap.id (_root_.Metric.sphere (0 : E) 1) := by
      apply ContinuousMap.ext
      exact hret
    have hmap : (integralSingularHomologyMap (n + 1) p).comp
        (integralSingularHomologyMap (n + 1) i) = LinearMap.id := by
      rw [← integralSingularHomologyMap_comp, hcomp, integralSingularHomologyMap_id]
    have hleft : Function.LeftInverse (integralSingularHomologyMap (n + 1) p)
        (integralSingularHomologyMap (n + 1) i) :=
      fun a ↦ LinearMap.congr_fun hmap a
    let := hleft.injective.subsingleton
    let : Subsingleton ℤ := (integralSphereTopHomologyEquiv n E hn).symm.injective.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FixedPoint.not_exists_retraction_closedBall_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FixedPoint.not_exists_retraction_closedBall_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FixedPoint.not_exists_retraction_closedBall_sphere ``Submission.DifferentialGeometry.Topology.FixedPoint.not_exists_retraction_closedBall_sphere

end DifferentialGeometry.Topology.FixedPoint
