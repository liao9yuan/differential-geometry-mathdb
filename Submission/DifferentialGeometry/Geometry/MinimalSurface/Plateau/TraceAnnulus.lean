import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastArea
import Submission.DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

theorem exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {σ : C(loopCircle, loopCircle)} (hσ : IsSmoothPositiveCircleMap σ)
    {u : C(closedDisk, M)} (htrace : diskTrace u = γ.comp σ)
    (hLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨ψ, hψ, _, _, hl, δ, hδ, Lδ, hδlip⟩ := hσ.exists_lipschitz_displacement
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨Lγ, hLγ⟩ := regularLoop_riemannian_lipschitz g
    (⟨γ, hγ.of_le (by simp)⟩ : regularLoop E M)
  obtain ⟨K, hK⟩ := tracePhaseAnnulus_lipschitzOn_strip g hLγ hδlip
  exact exists_spanningDiskCompetitor_of_tracePhase_lipschitz g hψ hl hδ hγ htrace hLip ⟨K, hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace ``Submission.DifferentialGeometry.Geometry.exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace

end DifferentialGeometry.Geometry
