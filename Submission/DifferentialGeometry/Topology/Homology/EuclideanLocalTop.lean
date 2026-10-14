import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Metric _root_.Module _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def integralEuclideanLocalTopGenerator (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x :=
  (integralEuclideanLocalTopEquiv E n hd x).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator


theorem integralEuclideanLocalTopGenerator_coordinate (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2)
    (x : E) :
    integralEuclideanLocalTopEquiv E n hd x (integralEuclideanLocalTopGenerator E n hd x) = 1 :=
  (integralEuclideanLocalTopEquiv E n hd x).apply_symm_apply 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_coordinate ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_coordinate


theorem integralEuclideanLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : _root_.Module.finrank ℝ E = n + 2) (x : E) :
    Function.Bijective (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) := by
  have hfun : (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) =
      ⇑(integralEuclideanLocalTopEquiv E n hd x).symm := by
    funext z
    apply (integralEuclideanLocalTopEquiv E n hd x).injective
    rw [map_zsmul, integralEuclideanLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralEuclideanLocalTopEquiv E n hd x).symm.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_zsmul_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_zsmul_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_zsmul_bijective ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_zsmul_bijective


theorem integralEuclideanLocalTopGenerator_ne_zero (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2) (x : E) :
    integralEuclideanLocalTopGenerator E n hd x ≠ 0 := by
  intro h
  have hh := congrArg (integralEuclideanLocalTopEquiv E n hd x) h
  rw [integralEuclideanLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_ne_zero ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopGenerator_ne_zero


def integralManifoldLocalTopGenerator (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x :=
  (integralManifoldLocalTopEquiv E n hd M x).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralManifoldLocalTopGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator ``Submission.DifferentialGeometry.Topology.integralManifoldLocalTopGenerator


theorem integralManifoldLocalTopGenerator_coordinate (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopEquiv E n hd M x (integralManifoldLocalTopGenerator E n hd M x) = 1 :=
  (integralManifoldLocalTopEquiv E n hd M x).apply_symm_apply 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_coordinate ``Submission.DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_coordinate


theorem integralManifoldLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : _root_.Module.finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M) :
    Function.Bijective (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) := by
  have hfun : (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) =
      ⇑(integralManifoldLocalTopEquiv E n hd M x).symm := by
    funext z
    apply (integralManifoldLocalTopEquiv E n hd M x).injective
    rw [map_zsmul, integralManifoldLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralManifoldLocalTopEquiv E n hd M x).symm.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_zsmul_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_zsmul_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_zsmul_bijective ``Submission.DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_zsmul_bijective


theorem integralManifoldLocalTopGenerator_ne_zero (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopGenerator E n hd M x ≠ 0 := by
  intro h
  have hh := congrArg (integralManifoldLocalTopEquiv E n hd M x) h
  rw [integralManifoldLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_ne_zero ``Submission.DifferentialGeometry.Topology.integralManifoldLocalTopGenerator_ne_zero


end DifferentialGeometry.Topology

end

end
