import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Mathlib.Analysis.Complex.RealDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


theorem DiskSmoothUpToBoundary.interior {u : C(closedDisk, M)}
    (h : DiskSmoothUpToBoundary (E := E) u) : DiskSmoothInterior (E := E) u :=
  h.mono Metric.ball_subset_closedBall

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.interior ``Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.interior


theorem diskBoundary_lift_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => (diskBoundary (t : loopCircle) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) := by
    have hreal : ContDiff ℝ ∞ (fun t : ℝ => (2 * Real.pi * t : ℝ)) := by fun_prop
    have hcomplex := Complex.ofRealCLM.contDiff.comp hreal
    exact Complex.contDiff_exp.comp (hcomplex.mul contDiff_const)
  exact h.contMDiff.congr (fun t => diskBoundary_coe t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskBoundary_lift_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskBoundary_lift_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskBoundary_lift_contMDiff ``Submission.DifferentialGeometry.Geometry.diskBoundary_lift_contMDiff



theorem DiskSmoothUpToBoundary.trace {u : C(closedDisk, M)}
    (h : DiskSmoothUpToBoundary (E := E) u) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => diskTrace u (t : loopCircle)) := by
  have hb := diskBoundary_lift_contMDiff
  have hc := h.comp_contMDiff hb (fun t => (diskBoundary (t : loopCircle)).property)
  apply hc.congr
  intro t
  exact (diskExtension_coe u (diskBoundary (t : loopCircle))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.trace ``Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.trace

end DifferentialGeometry.Geometry
