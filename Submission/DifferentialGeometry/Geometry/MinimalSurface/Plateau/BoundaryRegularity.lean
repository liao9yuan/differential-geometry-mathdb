import Submission.DifferentialGeometry.Geometry.HarmonicMap.DiskBoundaryRegularity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.ContinuousMap _root_.Set
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]



theorem IsMorreyDisk.exists_smooth_extension (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := by
  have htrace : ∀ z : ℂ, ‖z‖ = 1 → diskExtension u z ∈ _root_.Set.range γ := by
    intro z hz
    let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hb : (diskBoundary θ : ℂ) = z := by
      have hc := congrArg (fun x : Circle => (x : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    obtain ⟨σ, _, hσ⟩ := hu.trace
    refine ⟨σ θ, ?_⟩
    have hv := congrArg (fun f : freeLoop M => f θ) hσ
    change u (diskBoundary θ) = γ (σ θ) at hv
    rw [← hb, diskExtension_coe]
    exact hv.symm
  have hreg : DiskSmoothUpToBoundary (E := E) u :=
    contMDiffOn_closedDisk_of_embedded_loop g (by norm_num : (0 : ℝ) < 1)
      hγ.embedding hγ.smooth hγ.immersed
      (u.continuous.comp diskRetraction_lipschitz.continuous).continuousOn hu.smoothInterior htrace
      (fun z hz => (hu.conformal z hz).1) (fun z hz => (hu.conformal z hz).2) hu.harmonic
  let : FiniteDimensional ℝ E := .of_finrank_pos (by rw [hd]; norm_num)
  obtain ⟨U, heq, N, hN, hDN, hU⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary hreg
  have hi : _root_.Set.EqOn U (diskExtension u) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (heq ⟨z, Metric.ball_subset_closedBall hz⟩).trans
      (diskExtension_coe u ⟨z, Metric.ball_subset_closedBall hz⟩).symm
  have hc := hi.of_subset_closure (hU.continuousOn.mono hDN)
    (u.continuous.comp diskRetraction_lipschitz.continuous).continuousOn
    Metric.ball_subset_closedBall (by rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
  exact ⟨U, fun z => (hc z.property).trans (diskExtension_coe u z), N, hN, hDN, hU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsMorreyDisk.exists_smooth_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsMorreyDisk.exists_smooth_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsMorreyDisk.exists_smooth_extension ``Submission.DifferentialGeometry.Geometry.IsMorreyDisk.exists_smooth_extension



theorem selectedMorreyDisk_smoothUpToBoundary (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    DiskSmoothUpToBoundary (E := E)
      (selectedMorreyDisk g hcomplete hregular γ hγ hfinite) := by
  obtain ⟨U, hU⟩ := IsMorreyDisk.exists_smooth_extension g hd hγ
    (selectedMorreyDisk_isMorrey g hcomplete hregular γ hγ hfinite)
  exact hU.smoothUpToBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.selectedMorreyDisk_smoothUpToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.selectedMorreyDisk_smoothUpToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.selectedMorreyDisk_smoothUpToBoundary ``Submission.DifferentialGeometry.Geometry.selectedMorreyDisk_smoothUpToBoundary

end DifferentialGeometry.Geometry
