import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskSmoothLipschitz
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem DiskWeakJordanTrace.of_diskTrace_eq {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : diskTrace u = γ) : DiskWeakJordanTrace γ u :=
  ⟨ContinuousMap.id loopCircle,
    ⟨fun t : ℝ => t, continuous_id, fun _ => rfl,
      Or.inl ⟨monotone_id, fun _ => rfl⟩⟩,
    h.trans (ContinuousMap.comp_id γ).symm⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskWeakJordanTrace
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskWeakJordanTrace.of_diskTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskWeakJordanTrace.of_diskTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskWeakJordanTrace.of_diskTrace_eq ``Submission.DifferentialGeometry.Geometry.DiskWeakJordanTrace.of_diskTrace_eq

theorem isMorreyDisk_of_minimizesLipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hsmoothInterior : DiskSmoothInterior (E := E) u)
    (hconformal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (hharmonic : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0)
    (hfiniteEnergy : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1))
    (htrace : DiskWeakJordanTrace γ u)
    (hminimizesLipschitz : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) →
      riemannianDiskArea g u ≤ riemannianDiskArea g v) :
    IsMorreyDisk g γ u :=
  ⟨hsmoothInterior, hconformal, hharmonic, hfiniteEnergy, htrace, hminimizesLipschitz,
    fun v hv htracev => hminimizesLipschitz v (DiskWeakJordanTrace.of_diskTrace_eq htracev)
      (hv.exists_lipschitz g)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isMorreyDisk_of_minimizesLipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isMorreyDisk_of_minimizesLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isMorreyDisk_of_minimizesLipschitz ``Submission.DifferentialGeometry.Geometry.isMorreyDisk_of_minimizesLipschitz

end DifferentialGeometry.Geometry
