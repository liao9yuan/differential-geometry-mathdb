import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}

def atTime (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) :
    PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) t) (L.atTime (I := I) t) phi where
  partialDiffeomorph := Phi.partialDiffeomorph
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime

@[simp] theorem atTime_partialDiffeomorph
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).partialDiffeomorph k = Phi.partialDiffeomorph k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_partialDiffeomorph ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_partialDiffeomorph


@[simp] theorem atTime_source
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).source k = Phi.source k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_source


@[simp] theorem atTime_target
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).target k = Phi.target k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_target ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_target


@[simp] theorem atTime_map
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).map k = Phi.map k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_map ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTime_map

end DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps

end
