import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import Mathlib.Topology.Order.IsLUB

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def riemannianDiskEnergy (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : closedDisk → M) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy

theorem riemannianDiskEnergy_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : closedDisk → M) : 0 ≤ riemannianDiskEnergy g u :=
  _root_.MeasureTheory.integral_nonneg fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg g (diskExtension u z) _)
      (metric_inner_self_nonneg g (diskExtension u z) _)) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_nonneg ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_nonneg

def weaklyMonotoneDiskCompetitors (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    Set C(closedDisk, M) :=
  {u | DiskWeakJordanTrace γ u ∧ ∃ L : ℝ≥0, ∀ z w : closedDisk,
    riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors ``Submission.DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors

theorem spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    spanningDiskCompetitors g γ ⊆ weaklyMonotoneDiskCompetitors g γ := by
  rintro u ⟨htrace, hLip⟩
  exact ⟨DiskWeakJordanTrace.of_diskTrace_eq htrace, hLip⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors ``Submission.DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors

theorem exists_weakly_monotone_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : ℕ → C(closedDisk, M),
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
        (𝓝 (_root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) '' weaklyMonotoneDiskCompetitors g γ))) := by
  classical
  have hnonempty : (weaklyMonotoneDiskCompetitors g γ).Nonempty :=
    hfinite.mono (spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors g γ)
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) '' weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g u
  obtain ⟨e, heanti, heconv, he⟩ :=
    exists_seq_tendsto_sInf (hnonempty.image (fun v : C(closedDisk, M) => riemannianDiskEnergy g v)) hbound
  choose u hu hue using he
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hue] using heanti
  · simpa only [hue] using heconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_weakly_monotone_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_weakly_monotone_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_weakly_monotone_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_weakly_monotone_disk_energy_minimizing_sequence

variable [FiniteDimensional ℝ E] [T3Space M]

theorem weaklyMonotoneDiskCompetitor_integrable_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨_, L, hL⟩ := hu
  exact integrable_diskMapEnergyDensity g hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitor_integrable_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitor_integrable_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitor_integrable_energy ``Submission.DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitor_integrable_energy

end DifferentialGeometry.Geometry

end

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem exists_bounded_weakly_monotone_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ (u : ℕ → C(closedDisk, M)) (B : ℝ), 0 ≤ B ∧
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension (u n)))
        (Metric.closedBall (0 : ℂ) 1)) ∧
      (∀ n, riemannianDiskEnergy g (u n) ≤ B) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
        (𝓝 (_root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
          weaklyMonotoneDiskCompetitors g γ))) := by
  obtain ⟨u, hu, hanti, hlim⟩ :=
    exists_weakly_monotone_disk_energy_minimizing_sequence g γ hfinite
  exact ⟨u, riemannianDiskEnergy g (u 0), riemannianDiskEnergy_nonneg g (u 0), hu,
    fun n => weaklyMonotoneDiskCompetitor_integrable_energy g (hu n),
    fun n => hanti (Nat.zero_le n), hanti, hlim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_bounded_weakly_monotone_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_bounded_weakly_monotone_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_bounded_weakly_monotone_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_bounded_weakly_monotone_disk_energy_minimizing_sequence

end DifferentialGeometry.Geometry

end
