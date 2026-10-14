import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy
import Submission.DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Submission.DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import Submission.DifferentialGeometry.Analysis.Integration.Measure.UniformIntegrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




structure IsSmoothEmbeddedLoop (γ : freeLoop M) : Prop where
  smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))
  embedding : Topology.IsEmbedding γ
  immersed : ∀ t : ℝ,
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop ``Submission.DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop



def DiskWeakJordanTrace (γ : freeLoop M) (u : C(closedDisk, M)) : Prop :=
  ∃ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ ∧ diskTrace u = γ.comp σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskWeakJordanTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskWeakJordanTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskWeakJordanTrace ``Submission.DifferentialGeometry.Geometry.DiskWeakJordanTrace






structure IsMorreyDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : C(closedDisk, M)) : Prop where
  smoothInterior : DiskSmoothInterior (E := E) u
  conformal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z
  harmonic : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0
  finiteEnergy : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1)
  trace : DiskWeakJordanTrace γ u
  minimizesLipschitz : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
    (∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) →
        riemannianDiskArea g u ≤ riemannianDiskArea g v
  minimizesSmooth : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v → diskTrace v = γ →
    riemannianDiskArea g u ≤ riemannianDiskArea g v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsMorreyDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsMorreyDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsMorreyDisk ``Submission.DifferentialGeometry.Geometry.IsMorreyDisk



theorem IsMorreyDisk.integrableArea {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (h : IsMorreyDisk g γ u) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  diskArea_integrable_of_conformal_energy g u h.conformal h.finiteEnergy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.IsMorreyDisk
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsMorreyDisk.integrableArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsMorreyDisk.integrableArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsMorreyDisk.integrableArea ``Submission.DifferentialGeometry.Geometry.IsMorreyDisk.integrableArea

theorem IsMorreyDisk.exists_pos_integral_energy_lt
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : IsMorreyDisk g γ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ a : ℂ,
      (∫ z in Metric.closedBall a r ∩ Metric.closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension u) z) < ε := by
  obtain ⟨r, hr, hbound⟩ := h.finiteEnergy.exists_pos_integral_norm_closedBall_lt hε
  refine ⟨r, hr, fun a => ?_⟩
  have hle := _root_.MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Metric.closedBall a r ∩ Metric.closedBall (0 : ℂ) 1))
    (diskMapEnergyDensity g (diskExtension u))
  rw [Real.norm_eq_abs] at hle
  exact ((le_abs_self _).trans hle).trans_lt (hbound a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsMorreyDisk.exists_pos_integral_energy_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsMorreyDisk.exists_pos_integral_energy_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsMorreyDisk.exists_pos_integral_energy_lt ``Submission.DifferentialGeometry.Geometry.IsMorreyDisk.exists_pos_integral_energy_lt

end DifferentialGeometry.Geometry
