import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Directional
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Submission.DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E]

theorem measurable_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u) :
    Measurable (diskMapEnergyDensity g u) := by
  have h1 := measurable_diskMapDirectionalEnergyDensity g hu
    (V := fun _ => (1 : ℂ)) measurable_const
  have hI := measurable_diskMapDirectionalEnergyDensity g hu
    (V := fun _ => Complex.I) measurable_const
  exact (h1.add hI).div_const 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.measurable_diskMapEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.measurable_diskMapEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.measurable_diskMapEnergyDensity ``Submission.DifferentialGeometry.Geometry.measurable_diskMapEnergyDensity

variable [T3Space M]

set_option backward.isDefEq.respectTransparency false in
theorem diskMapEnergyDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (z : ℂ) : diskMapEnergyDensity g u z ≤ (C : ℝ) ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := (Module.finrank_zero_iff).mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (u z)) := ‹Subsingleton E›
    have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z = 0 := by ext; exact Subsingleton.elim _ _
    simp [diskMapEnergyDensity, diskMapPartial, hzero, zero_apply, map_zero]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
    · have h₁ := sqrt_metric_mfderiv_le g hu hd (1 : ℂ)
      have hI := sqrt_metric_mfderiv_le g hu hd Complex.I
      simp only [_root_.NormOneClass.norm_one, Complex.norm_I, mul_one] at h₁ hI
      have h₁sq := sq_le_sq₀ (Real.sqrt_nonneg _) C.coe_nonneg |>.mpr h₁
      have hIsq := sq_le_sq₀ (Real.sqrt_nonneg _) C.coe_nonneg |>.mpr hI
      rw [Real.sq_sqrt (metric_inner_self_nonneg g (u z) _)] at h₁sq hIsq
      unfold diskMapEnergyDensity diskMapPartial
      linarith
    · simp [diskMapEnergyDensity, diskMapPartial, mfderiv_zero_of_not_mdifferentiableAt hd,
          zero_apply, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapEnergyDensity_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapEnergyDensity_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapEnergyDensity_le_of_lipschitz ``Submission.DifferentialGeometry.Geometry.diskMapEnergyDensity_le_of_lipschitz

theorem integrableOn_diskMapEnergyDensity_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (s : Set ℂ) {μ : _root_.MeasureTheory.Measure ℂ} [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict s)] :
    IntegrableOn (diskMapEnergyDensity g u) s μ := by
  have hm := measurable_diskMapEnergyDensity g (continuous_of_riemannian_lipschitz g hu)
  apply Integrable.mono' (_root_.MeasureTheory.integrable_const ((C : ℝ) ^ 2)) hm.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    have hn : 0 ≤ diskMapEnergyDensity g u z :=
      div_nonneg (add_nonneg (metric_inner_self_nonneg g (u z) _)
        (metric_inner_self_nonneg g (u z) _)) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact diskMapEnergyDensity_le_of_lipschitz g hu z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrableOn_diskMapEnergyDensity_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrableOn_diskMapEnergyDensity_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrableOn_diskMapEnergyDensity_of_lipschitz ``Submission.DifferentialGeometry.Geometry.integrableOn_diskMapEnergyDensity_of_lipschitz

theorem integrable_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  exact integrableOn_diskMapEnergyDensity_of_lipschitz g (diskExtension_riemannian_lipschitz g hu) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity ``Submission.DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity


theorem integral_diskMapEnergyDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (s : Set ℂ) {μ : _root_.MeasureTheory.Measure ℂ} [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict s)] :
    ∫ z in s, diskMapEnergyDensity g u z ∂μ ≤ (C : ℝ) ^ 2 * μ.real s := by
  have hi := _root_.MeasureTheory.integral_mono (integrableOn_diskMapEnergyDensity_of_lipschitz g hu s (μ := μ))
    (_root_.MeasureTheory.integrable_const ((C : ℝ) ^ 2)) (diskMapEnergyDensity_le_of_lipschitz g hu)
  simpa only [_root_.MeasureTheory.integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_comm,
    Measure.real] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_diskMapEnergyDensity_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_diskMapEnergyDensity_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_diskMapEnergyDensity_le_of_lipschitz ``Submission.DifferentialGeometry.Geometry.integral_diskMapEnergyDensity_le_of_lipschitz

theorem spanningDiskCompetitor_integrable_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨_, L, hL⟩ := hu
  exact integrable_diskMapEnergyDensity g hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskCompetitor_integrable_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskCompetitor_integrable_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskCompetitor_integrable_energy ``Submission.DifferentialGeometry.Geometry.spanningDiskCompetitor_integrable_energy

end DifferentialGeometry.Geometry
