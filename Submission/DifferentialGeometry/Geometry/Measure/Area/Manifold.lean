import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import Submission.DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def riemannianArea (g : SmoothRiemannianMetric I M) (u : ℂ → M) (s : Set ℂ) : ℝ :=
  ∫ z in s, riemannianAreaDensity g u z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea ``Submission.DifferentialGeometry.Geometry.riemannianArea

theorem riemannianArea_nonneg (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) (s : Set ℂ) : 0 ≤ riemannianArea g u s :=
  _root_.MeasureTheory.integral_nonneg (fun z => riemannianAreaDensity_nonneg g u z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_nonneg ``Submission.DifferentialGeometry.Geometry.riemannianArea_nonneg

@[simp] theorem riemannianArea_const (g : SmoothRiemannianMetric I M)
    (q : M) (s : Set ℂ) : riemannianArea g (fun _ => q) s = 0 := by
  simp [riemannianArea]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_const ``Submission.DifferentialGeometry.Geometry.riemannianArea_const

theorem riemannianArea_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (u : ℂ → M) (s : Set ℂ) :
    riemannianArea (scaleMetric c hc g) u s = c * riemannianArea g u s := by
  simp only [riemannianArea, riemannianAreaDensity_scaleMetric, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_scaleMetric ``Submission.DifferentialGeometry.Geometry.riemannianArea_scaleMetric


def riemannianDiskArea (g : SmoothRiemannianMetric I M) (u : closedDisk → M) : ℝ :=
  riemannianArea g (diskExtension u) (Metric.closedBall 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea



theorem riemannianDiskArea_eq_of_extension (g : SmoothRiemannianMetric I M)
    (u : closedDisk → M) (U : ℂ → M) (hU : ∀ z : closedDisk, U z = u z) :
    riemannianDiskArea g u = riemannianArea g U (Metric.closedBall 0 1) := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  apply riemannianAreaDensity_congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  have hw' := Metric.ball_subset_closedBall hw
  exact (diskExtension_coe u ⟨w, hw'⟩).trans (hU ⟨w, hw'⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_eq_of_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_eq_of_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_eq_of_extension ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_eq_of_extension

theorem riemannianDiskArea_nonneg (g : SmoothRiemannianMetric I M)
    (u : closedDisk → M) : 0 ≤ riemannianDiskArea g u := riemannianArea_nonneg _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_nonneg ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_nonneg

@[simp] theorem riemannianDiskArea_const (g : SmoothRiemannianMetric I M)
    (q : M) : riemannianDiskArea g (fun _ => q) = 0 := riemannianArea_const _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_const ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_const

theorem riemannianDiskArea_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (u : closedDisk → M) :
    riemannianDiskArea (scaleMetric c hc g) u = c * riemannianDiskArea g u :=
  riemannianArea_scaleMetric _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_scaleMetric ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_scaleMetric

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_riemannianAreaDensity (g : SmoothRiemannianMetric I M)
    {u : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) :
    ContinuousOn (riemannianAreaDensity g u) s := by
  have ht := hu.continuousOn_tangentMapWithin le_rfl hs.uniqueMDiffOn
  have hv (v : ℂ) : ContinuousOn (fun z : ℂ =>
      TotalSpace.mk' E (u z) (mfderiv 𝓘(ℝ, ℂ) I u z v)) s := by
    have hinput : Continuous (fun z : ℂ =>
        (TotalSpace.mk' ℂ z v : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hc := ht.comp hinput.continuousOn (fun _ hz => hz)
    apply hc.congr
    intro z hz
    dsimp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hz)]
  exact continuousOn_tangentTwoJacobian g (hv 1) (hv Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_riemannianAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_riemannianAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_riemannianAreaDensity ``Submission.DifferentialGeometry.Geometry.continuousOn_riemannianAreaDensity



theorem integrableOn_riemannianAreaDensity_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {u : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s)
    (hK : IsCompact K) (hKs : K ⊆ s) : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity g u) K :=
  ((continuousOn_riemannianAreaDensity g hs hu).mono hKs).integrableOn_compact hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrableOn_riemannianAreaDensity_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrableOn_riemannianAreaDensity_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrableOn_riemannianAreaDensity_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.integrableOn_riemannianAreaDensity_of_contMDiffOn


theorem riemannianArea_union (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) {s t : Set ℂ} (hs : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity g u) s)
    (ht : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity g u) t)
    (hst : _root_.MeasureTheory.AEDisjoint _root_.MeasureTheory.MeasureSpace.volume s t) (htm : MeasurableSet t) :
    riemannianArea g u (s ∪ t) = riemannianArea g u s + riemannianArea g u t :=
  _root_.MeasureTheory.setIntegral_union₀ hst htm.nullMeasurableSet hs ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_union ``Submission.DifferentialGeometry.Geometry.riemannianArea_union

end DifferentialGeometry.Geometry
