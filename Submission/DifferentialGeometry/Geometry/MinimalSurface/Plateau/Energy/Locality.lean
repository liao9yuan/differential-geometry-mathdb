import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U W : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] W) : diskMapEnergyDensity g U z = diskMapEnergyDensity g W z := by
  unfold diskMapEnergyDensity diskMapPartial
  erw [h.mfderiv_eq, h.eq_of_nhds]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapEnergyDensity_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapEnergyDensity_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapEnergyDensity_congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.diskMapEnergyDensity_congr_of_eventuallyEq

theorem riemannianDiskEnergy_eq_integral_of_eqOn_openDisk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {U : ℂ → M}
    (heq : _root_.Set.EqOn (diskExtension u) U (Metric.ball (0 : ℂ) 1)) :
    riemannianDiskEnergy g u = ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g U z := by
  unfold riemannianDiskEnergy
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  apply diskMapEnergyDensity_congr_of_eventuallyEq g
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact heq hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_integral_of_eqOn_openDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_integral_of_eqOn_openDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_integral_of_eqOn_openDisk ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_integral_of_eqOn_openDisk


theorem riemannianDiskEnergy_comp_eq_of_extensions
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : ∀ z : closedDisk, U z = u z) (φ : C(closedDisk, closedDisk)) {Φ : ℂ → ℂ}
    (hφ : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1),
      (φ ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = Φ z) :
    riemannianDiskEnergy g (u.comp φ) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (U ∘ Φ) z := by
  apply riemannianDiskEnergy_eq_integral_of_eqOn_openDisk g
  intro z hz
  rw [show diskExtension (u.comp φ) z = u (φ ⟨z, Metric.ball_subset_closedBall hz⟩) from
    diskExtension_coe (u.comp φ) ⟨z, Metric.ball_subset_closedBall hz⟩]
  rw [← hu (φ ⟨z, Metric.ball_subset_closedBall hz⟩), hφ z hz]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_comp_eq_of_extensions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_comp_eq_of_extensions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_comp_eq_of_extensions ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_comp_eq_of_extensions

end DifferentialGeometry.Geometry

end

end
