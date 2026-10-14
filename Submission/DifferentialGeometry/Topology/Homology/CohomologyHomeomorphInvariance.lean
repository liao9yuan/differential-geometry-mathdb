import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def integralSingularCohomologyEquivOfHomeomorph (e : X ≃ₜ Y) (n : ℕ) :
    integralSingularCohomology n X ≃ₗ[ℤ] integralSingularCohomology n Y where
  toFun := ⇑(integralSingularCohomologyMap n (e.symm : C(Y, X)))
  invFun := ⇑(integralSingularCohomologyMap n (e : C(X, Y)))
  map_add' := (integralSingularCohomologyMap n (e.symm : C(Y, X))).map_add
  map_smul' := (integralSingularCohomologyMap n (e.symm : C(Y, X))).map_smul
  left_inv a := by
    have hcomp : (integralSingularCohomologyMap n (e : C(X, Y))).comp
        (integralSingularCohomologyMap n (e.symm : C(Y, X))) = LinearMap.id := by
      have h : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X :=
        ContinuousMap.ext fun x => e.left_inv x
      calc
        (integralSingularCohomologyMap n (e : C(X, Y))).comp
            (integralSingularCohomologyMap n (e.symm : C(Y, X)))
            = integralSingularCohomologyMap n ((e.symm : C(Y, X)).comp (e : C(X, Y))) :=
              (integralSingularCohomologyMap_comp n (e : C(X, Y)) (e.symm : C(Y, X))).symm
        _ = integralSingularCohomologyMap n (ContinuousMap.id X) := by rw [h]
        _ = LinearMap.id := integralSingularCohomologyMap_id n
    exact LinearMap.congr_fun hcomp a
  right_inv a := by
    have hcomp : (integralSingularCohomologyMap n (e.symm : C(Y, X))).comp
        (integralSingularCohomologyMap n (e : C(X, Y))) = LinearMap.id := by
      have h : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y :=
        ContinuousMap.ext fun y => e.right_inv y
      calc
        (integralSingularCohomologyMap n (e.symm : C(Y, X))).comp
            (integralSingularCohomologyMap n (e : C(X, Y)))
            = integralSingularCohomologyMap n ((e : C(X, Y)).comp (e.symm : C(Y, X))) :=
              (integralSingularCohomologyMap_comp n (e.symm : C(Y, X)) (e : C(X, Y))).symm
        _ = integralSingularCohomologyMap n (ContinuousMap.id Y) := by rw [h]
        _ = LinearMap.id := integralSingularCohomologyMap_id n
    exact LinearMap.congr_fun hcomp a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyEquivOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyEquivOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyEquivOfHomeomorph ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyEquivOfHomeomorph

theorem subsingleton_integralSingularCohomology_of_homeomorph (e : X ≃ₜ Y) (n : ℕ)
    [Subsingleton (integralSingularCohomology n X)] :
    Subsingleton (integralSingularCohomology n Y) :=
  (integralSingularCohomologyEquivOfHomeomorph e n).surjective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularCohomology_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularCohomology_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularCohomology_of_homeomorph ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularCohomology_of_homeomorph

end DifferentialGeometry.Topology
