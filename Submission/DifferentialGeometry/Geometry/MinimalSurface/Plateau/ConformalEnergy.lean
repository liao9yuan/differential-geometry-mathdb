import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.ConformalPair
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem DiskMapConformalAt.areaDensity_eq_energy
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    riemannianAreaDensity g U z = diskMapEnergyDensity g U z := by
  have ha : riemannianAreaDensity g U z =
      g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) :=
    tangentTwoJacobian_of_conformal g h.1 h.2
  rw [ha]
  unfold diskMapEnergyDensity
  rw [← h.2]
  ring

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskMapConformalAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.areaDensity_eq_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.areaDensity_eq_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.areaDensity_eq_energy ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.areaDensity_eq_energy

theorem DiskMapConformalAt.energy_le_sum_sub_smul
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) (t : TangentSpace 𝓘(ℝ, E) (U z)) (a b : ℝ) :
    diskMapEnergyDensity g U z ≤
      g.inner (U z) (diskMapPartial U z 1 - a • t) (diskMapPartial U z 1 - a • t) +
        g.inner (U z) (diskMapPartial U z Complex.I - b • t)
          (diskMapPartial U z Complex.I - b • t) := by
  have hB : (Tensor0SBundle.tangentFlatLinear g (U z)).IsPosSemidef :=
    ⟨⟨g.symm (U z)⟩, ⟨metric_inner_self_nonneg g (U z)⟩⟩
  have hbound := hB.apply_self_le_sum_sub_smul_of_orthogonal h.1 h.2 t a b
  simp only [Tensor0SBundle.tangentFlatLinear_apply] at hbound
  unfold diskMapEnergyDensity
  rw [← h.2, add_self_div_two]
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.energy_le_sum_sub_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.energy_le_sum_sub_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.energy_le_sum_sub_smul ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.energy_le_sum_sub_smul



theorem diskAreaDensity_ae_eq_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    riemannianAreaDensity g (diskExtension u) =ᵐ[volume.restrict (Metric.closedBall 0 1)]
      diskMapEnergyDensity g (diskExtension u) := by
  filter_upwards [ae_disk_interior] with z hz
  exact (h z hz).areaDensity_eq_energy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskAreaDensity_ae_eq_energy_of_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskAreaDensity_ae_eq_energy_of_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskAreaDensity_ae_eq_energy_of_conformal ``Submission.DifferentialGeometry.Geometry.diskAreaDensity_ae_eq_energy_of_conformal



theorem diskArea_integrable_iff_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) ↔
      IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  _root_.MeasureTheory.integrable_congr (diskAreaDensity_ae_eq_energy_of_conformal g u h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskArea_integrable_iff_energy_of_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskArea_integrable_iff_energy_of_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskArea_integrable_iff_energy_of_conformal ``Submission.DifferentialGeometry.Geometry.diskArea_integrable_iff_energy_of_conformal

theorem diskArea_integrable_of_conformal_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (he : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1)) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  (diskArea_integrable_iff_energy_of_conformal g u h).2 he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskArea_integrable_of_conformal_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskArea_integrable_of_conformal_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskArea_integrable_of_conformal_energy ``Submission.DifferentialGeometry.Geometry.diskArea_integrable_of_conformal_energy


theorem riemannianDiskArea_eq_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    riemannianDiskArea g u =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z :=
  _root_.MeasureTheory.integral_congr_ae (diskAreaDensity_ae_eq_energy_of_conformal g u h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_eq_energy_of_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_eq_energy_of_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_eq_energy_of_conformal ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_eq_energy_of_conformal

end DifferentialGeometry.Geometry
