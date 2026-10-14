import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.TraceAnnulus
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]



theorem IsConformalMinimizingDisk.area_eq_leastSpanningArea
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : lipschitzContractibleLoop g}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ.val.val (t : loopCircle)))
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ.val.val u σ U) :
    riemannianDiskArea g u = leastSpanningArea g γ := by
  obtain ⟨v, hv, harea⟩ :=
    exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace
      g hγ h.positiveTrace h.trace
    (h.extension.lipschitz g)
  apply le_antisymm
  · apply le_csInf (show (spanningDiskAreas g γ).Nonempty from ⟨_, v, hv, rfl⟩)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨wj, hwj, ht⟩ := exists_smooth_spanning_disks_tendsto_area g hγ hw
    exact ge_of_tendsto ht (Eventually.of_forall fun j =>
      h.minimizesSmooth (wj j) (hwj j).1 (hwj j).2)
  · exact harea ▸ leastSpanningArea_le_competitor g γ hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.area_eq_leastSpanningArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsConformalMinimizingDisk.area_eq_leastSpanningArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.area_eq_leastSpanningArea ``Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk.area_eq_leastSpanningArea

end DifferentialGeometry.Geometry
