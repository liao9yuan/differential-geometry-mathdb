import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.PositiveTrace
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExactAttainment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]




theorem selectedMorreyDisk_conformal_output (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = selectedMorreyDisk g hcomplete hregular γ hγ hfinite ∨
        v = (selectedMorreyDisk g hcomplete hregular γ hγ hfinite).comp
          ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v =
        riemannianDiskArea g (selectedMorreyDisk g hcomplete hregular γ hγ hfinite) ∧
      IsConformalMinimizingDisk g γ v σ U := by
  have hu := selectedMorreyDisk_isMorrey g hcomplete hregular γ hγ hfinite
  exact hu.exists_conformal_minimizing_disk g hd hγ
    (hu.exists_smooth_extension g hd hγ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.selectedMorreyDisk_conformal_output then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.selectedMorreyDisk_conformal_output"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.selectedMorreyDisk_conformal_output ``Submission.DifferentialGeometry.Geometry.selectedMorreyDisk_conformal_output



theorem selectedMorreyDisk_area_eq_leastSpanningArea [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : lipschitzContractibleLoop g) (hγ : IsSmoothEmbeddedLoop (E := E) γ.val.val)
    (hfinite : (spanningDiskCompetitors g γ.val.val).Nonempty) :
    riemannianDiskArea g
      (selectedMorreyDisk g hcomplete hregular γ.val.val hγ hfinite) =
      leastSpanningArea g γ := by
  obtain ⟨v, σ, U, _, heq, hv⟩ := selectedMorreyDisk_conformal_output g hd hcomplete hregular
    γ.val.val hγ hfinite
  exact heq.symm.trans (hv.area_eq_leastSpanningArea hγ.smooth)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.selectedMorreyDisk_area_eq_leastSpanningArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.selectedMorreyDisk_area_eq_leastSpanningArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.selectedMorreyDisk_area_eq_leastSpanningArea ``Submission.DifferentialGeometry.Geometry.selectedMorreyDisk_area_eq_leastSpanningArea

end DifferentialGeometry.Geometry
