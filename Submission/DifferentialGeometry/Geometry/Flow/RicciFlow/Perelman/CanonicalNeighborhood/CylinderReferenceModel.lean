import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Curvature.Product
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarSectional
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology
open scoped _root_.Bundle _root_.Submission.Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance cylinderSphereTwoFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderSphereTwoFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderSphereTwoFact target :: scope.openDecls } }

def cylinderReferenceMetric (s : ℝ) : SmoothRiemannianMetric IC Cylinder :=
  cylinderMetric (I := I2)
    (scaleMetric (I := I2) (_root_.Max.max (2 * (1 - s)) 1)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric

theorem cylinderReferenceMetric_inner (s : ℝ) (hs : s ≤ 0) (y : Cylinder)
    (v w : TangentSpace IC y) :
    (cylinderReferenceMetric s).inner y v w =
      2 * (1 - s) *
        _root_.Inner.inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 v.1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 w.1)
      + v.2 * w.2 := by
  have hmax : _root_.Max.max (2 * (1 - s)) 1 = 2 * (1 - s) := by
    apply max_eq_left
    linarith
  simp only [cylinderReferenceMetric, cylinderMetric_inner, hmax]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_inner

theorem cylinderReferenceMetric_zero_inner (y : Cylinder) (v w : TangentSpace IC y) :
    (cylinderReferenceMetric 0).inner y v w =
      2 * _root_.Inner.inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 v.1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 w.1)
      + v.2 * w.2 := by
  simpa using cylinderReferenceMetric_inner 0 le_rfl y v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_inner

theorem CylinderReference.metric_zero_eq_roundCylinder (C : CylinderReference) :
    C.metric 0 = DifferentialGeometry.Geometry.Metric.roundCylinderMetric
      (E := ThreeSpace) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [C.inner_eq 0 le_rfl, DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner]
  norm_num
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.metric_zero_eq_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.metric_zero_eq_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.metric_zero_eq_roundCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.metric_zero_eq_roundCylinder


theorem cylinderReferenceMetric_scalar (s : ℝ) (hs : s ≤ 0) (y : Cylinder) :
    metricScalarAt (cylinderReferenceMetric s) y = (1 - s)⁻¹ := by
  have hmax : _root_.Max.max (2 * (1 - s)) 1 = 2 * (1 - s) := by
    apply max_eq_left
    linarith
  have hround : metricScalarAt (I := I2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) y.1 = 2 := by
    have h := metricScalarAt_of_constant_sectional
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) y.1 1
      (fun u v => by
        rw [roundMetric_sec_value (E := EuclideanSpace ℝ (Fin 3)) (n := 2) y.1 u v, one_mul]
        ring)
    rw [h, finrank_euclideanSpace_fin]
    norm_num
  rw [cylinderReferenceMetric, cylinderMetric, metricScalarAt_productMetric,
    metricScalarAt_scaleMetric, hmax, hround,
    metricScalarAt_eq_zero_of_finrank_le_one _ (by simp) y.2, add_zero]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar

theorem cylinderReferenceMetric_zero_scalar (y : Cylinder) :
    metricScalarAt (cylinderReferenceMetric 0) y = 1 := by
  simpa using cylinderReferenceMetric_scalar 0 le_rfl y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_scalar

def cylinderReference : CylinderReference where
  metric := cylinderReferenceMetric
  inner_eq := fun s hs y v w => cylinderReferenceMetric_inner s hs y v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReference ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReference

theorem nonempty_cylinderReference : Nonempty CylinderReference :=
  ⟨cylinderReference⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_cylinderReference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_cylinderReference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_cylinderReference ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_cylinderReference

theorem cylinderReferenceMetric_scalar_pos (s : ℝ) (hs : s ≤ 0) (y : Cylinder) :
    0 < metricScalarAt (cylinderReferenceMetric s) y := by
  rw [cylinderReferenceMetric_scalar s hs y]
  exact inv_pos.mpr (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_scalar_pos

theorem cylinderReferenceMetric_zero_ne_neg_one (y : Cylinder) :
    cylinderReferenceMetric 0 ≠ cylinderReferenceMetric (-1) := by
  intro h
  have h1 : metricScalarAt (cylinderReferenceMetric 0) y = 1 :=
    cylinderReferenceMetric_zero_scalar y
  have h2 : metricScalarAt (cylinderReferenceMetric (-1)) y = 1 / 2 := by
    rw [cylinderReferenceMetric_scalar (-1) (by norm_num) y]
    norm_num
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_ne_neg_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_ne_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_ne_neg_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderReferenceMetric_zero_ne_neg_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
