import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.AreaEnergy
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeakJordanDensity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.ContDiff _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem disk_energy_inf_le_area_of_weakJordanTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) :
    _root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskArea g u := by
  obtain ⟨vj, Vj, hj, ht⟩ :=
    exists_smooth_spanning_disks_tendsto_area_of_weakJordanTrace g hγ him hu hL
  exact ge_of_tendsto' ht (fun j =>
    (hj j).1.disk_energy_inf_le_area g (DiskWeakJordanTrace.of_diskTrace_eq (hj j).2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.disk_energy_inf_le_area_of_weakJordanTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.disk_energy_inf_le_area_of_weakJordanTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.disk_energy_inf_le_area_of_weakJordanTrace ``Submission.DifferentialGeometry.Geometry.disk_energy_inf_le_area_of_weakJordanTrace

theorem riemannianDiskArea_le_of_energy_attainment_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)}
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (heq : riemannianDiskEnergy g u = _root_.InfSet.sInf
      ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))
    {v : C(closedDisk, M)} (hv : DiskWeakJordanTrace γ v) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) :
    riemannianDiskArea g u ≤ riemannianDiskArea g v := by
  have harea : riemannianDiskArea g u = riemannianDiskEnergy g u :=
    riemannianDiskArea_eq_energy_of_conformal g u hconf
  rw [harea, heq]
  exact disk_energy_inf_le_area_of_weakJordanTrace g hγ him hv hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_le_of_energy_attainment_of_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_le_of_energy_attainment_of_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_le_of_energy_attainment_of_conformal ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_le_of_energy_attainment_of_conformal

theorem isMorreyDisk_of_energy_attainment
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hsmooth : DiskSmoothInterior (E := E) u)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0)
    (hfinite : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1))
    (htrace : DiskWeakJordanTrace γ u)
    (heq : riemannianDiskEnergy g u = _root_.InfSet.sInf
      ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ)) :
    IsMorreyDisk g γ u := by
  have hmin : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) →
      riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    rintro v hv ⟨L, hL⟩
    exact riemannianDiskArea_le_of_energy_attainment_of_conformal g hγ him hconf heq hv hL
  refine ⟨hsmooth, hconf, hharm, hfinite, htrace, hmin, ?_⟩
  intro v hv hboundary
  obtain ⟨V, hV⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary hv
  exact hmin v (DiskWeakJordanTrace.of_diskTrace_eq hboundary) (hV.lipschitz g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isMorreyDisk_of_energy_attainment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isMorreyDisk_of_energy_attainment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isMorreyDisk_of_energy_attainment ``Submission.DifferentialGeometry.Geometry.isMorreyDisk_of_energy_attainment

end DifferentialGeometry.Geometry

end

end
