import Submission.DifferentialGeometry.Analysis.Integration.BallBoundary
import Submission.DifferentialGeometry.Geometry.Measure.Area.Euclidean
import Submission.DifferentialGeometry.Geometry.Metric.ConvexProjection
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission













noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.MeasureTheory.Measure _root_.Set _root_.Filter _root_.ContinuousMap _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Geometry


def diskRetraction : ℂ → closedDisk :=
  convexProjection ⟨0, by simp⟩ isClosed_closedBall.isComplete (convex_closedBall (0 : ℂ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskRetraction ``Submission.DifferentialGeometry.Geometry.diskRetraction

theorem diskRetraction_lipschitz : LipschitzWith 1 diskRetraction :=
  convexProjection_lipschitz _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskRetraction_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskRetraction_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskRetraction_lipschitz ``Submission.DifferentialGeometry.Geometry.diskRetraction_lipschitz

@[simp] theorem diskRetraction_coe (z : closedDisk) : diskRetraction z = z :=
  convexProjection_of_mem _ _ _ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskRetraction_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskRetraction_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskRetraction_coe ``Submission.DifferentialGeometry.Geometry.diskRetraction_coe


def diskExtension {Q : Type*} (u : closedDisk → Q) : ℂ → Q := u ∘ diskRetraction

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskExtension ``Submission.DifferentialGeometry.Geometry.diskExtension

@[simp] theorem diskExtension_coe {Q : Type*} (u : closedDisk → Q) (z : closedDisk) :
    diskExtension u z = u z := by simp [diskExtension]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskExtension_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskExtension_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskExtension_coe ``Submission.DifferentialGeometry.Geometry.diskExtension_coe

theorem diskExtension_lipschitz {Q : Type*} [PseudoMetricSpace Q]
    {u : closedDisk → Q} {C : ℝ≥0} (hu : LipschitzWith C u) : LipschitzWith C (diskExtension u) := by
  simpa [diskExtension] using hu.comp diskRetraction_lipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskExtension_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskExtension_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskExtension_lipschitz ``Submission.DifferentialGeometry.Geometry.diskExtension_lipschitz


theorem ae_disk_interior : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
    z ∈ Metric.ball (0 : ℂ) 1 :=
  ae_mem_ball_of_measure_sphere_eq_zero (_root_.MeasureTheory.Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ae_disk_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ae_disk_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ae_disk_interior ``Submission.DifferentialGeometry.Geometry.ae_disk_interior


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]


def euclideanDiskArea (u : closedDisk → E) : ℝ :=
  euclideanArea (diskExtension u) (Metric.closedBall 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea



theorem euclideanDiskArea_eq_of_extension (u : closedDisk → E) (U : ℂ → E)
    (hU : ∀ z : closedDisk, U z = u z) :
    euclideanDiskArea u = euclideanArea U (Metric.closedBall 0 1) := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  have heq : diskExtension u =ᶠ[𝓝 z] U := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have hw' := Metric.ball_subset_closedBall hw
    exact (diskExtension_coe u ⟨w, hw'⟩).trans (hU ⟨w, hw'⟩).symm
  simp only [euclideanAreaDensity, heq.fderiv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea_eq_of_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea_eq_of_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea_eq_of_extension ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea_eq_of_extension

theorem euclideanDiskArea_nonneg (u : closedDisk → E) : 0 ≤ euclideanDiskArea u :=
  euclideanArea_nonneg _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea_nonneg ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea_nonneg

@[simp] theorem euclideanDiskArea_const (q : E) : euclideanDiskArea (fun _ => q) = 0 :=
  euclideanArea_const q _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea_const ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea_const

theorem euclideanDiskArea_smul (u : closedDisk → E) (c : ℝ) :
    euclideanDiskArea (c • u) = c ^ 2 * euclideanDiskArea u :=
  euclideanArea_smul (diskExtension u) c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea_smul ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea_smul

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

local instance _root_.Submission.DifferentialGeometry.Geometry.instIsFiniteMeasureComplexRestrictVolumeClosedBallOfNatReal_differentialGeometry : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instIsFiniteMeasureComplexRestrictVolumeClosedBallOfNatReal_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instIsFiniteMeasureComplexRestrictVolumeClosedBallOfNatReal_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instIsFiniteMeasureComplexRestrictVolumeClosedBallOfNatReal_differentialGeometry ``Submission.DifferentialGeometry.Geometry.instIsFiniteMeasureComplexRestrictVolumeClosedBallOfNatReal_differentialGeometry

theorem integrable_euclideanDiskAreaDensity {u : closedDisk → E} {C : ℝ≥0}
    (hu : LipschitzWith C u) :
    IntegrableOn (euclideanAreaDensity (diskExtension u)) (Metric.closedBall 0 1) :=
  integrableOn_euclideanAreaDensity (diskExtension_lipschitz hu) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_euclideanDiskAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_euclideanDiskAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_euclideanDiskAreaDensity ``Submission.DifferentialGeometry.Geometry.integrable_euclideanDiskAreaDensity


theorem euclideanDiskArea_comp_le {u : closedDisk → E} {f : E → F} {C L : ℝ≥0}
    (hu : LipschitzWith C u) (hf : LipschitzWith L f) :
    euclideanDiskArea (f ∘ u) ≤ (L : ℝ) ^ 2 * euclideanDiskArea u :=
  euclideanArea_comp_le (diskExtension_lipschitz hu) hf _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanDiskArea_comp_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanDiskArea_comp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanDiskArea_comp_le ``Submission.DifferentialGeometry.Geometry.euclideanDiskArea_comp_le

end FiniteDimensional

end DifferentialGeometry.Geometry
