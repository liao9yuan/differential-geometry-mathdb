import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionPairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem fderiv_diskMapMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q w) (diskMapPartial U q x)) z v =
      g.inner (U z) (diskMapCovariantPartial g U z v w) (diskMapPartial U z x) +
      g.inner (U z) (diskMapPartial U z w) (diskMapCovariantPartial g U z v x) := by
  exact fderiv_sourceSectionPairing g hs hU
    (contMDiffOn_source_partial hs hU (by simp) w)
    (contMDiffOn_source_partial hs hU (by simp) x) hz v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.fderiv_diskMapMetricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.fderiv_diskMapMetricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.fderiv_diskMapMetricPairing ``Submission.DifferentialGeometry.Geometry.fderiv_diskMapMetricPairing




theorem fderiv_diskMapConformalCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    fderiv ℝ (diskMapConformalCoefficient g U) z v =
      2 * g.inner (U z) (diskMapCovariantPartial g U z v 1) (diskMapPartial U z 1) := by
  change fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)) z v = _
  rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (diskMapPartial U z 1)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.fderiv_diskMapConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.fderiv_diskMapConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.fderiv_diskMapConformalCoefficient ``Submission.DifferentialGeometry.Geometry.fderiv_diskMapConformalCoefficient

end DifferentialGeometry.Geometry
