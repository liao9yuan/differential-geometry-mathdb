import Submission.DifferentialGeometry.Geometry.Metric.SourceCoefficients
import Submission.DifferentialGeometry.Topology.Manifold.AffineCharts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis

variable {A E V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem iteratedFDeriv_affineChart_metricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : OpenPartialHomeomorph A M}
    (hc : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ c c.source)
    (a : A) (L : V ≃L[ℝ] A) {x : V} (hx : a + L x ∈ c.source) (v w : V) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => g.inner (affineChart c a L y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y w)) x =
      (iteratedFDeriv ℝ k (fun y => g.inner (c y)
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L v))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L w))) (a + L x)).compContinuousLinearMap
          (fun _ : Fin k => (L : V →L[ℝ] A)) := by
  let H : A → ℝ := fun y => g.inner (c y)
    (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L v)) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L w))
  have hH : ContDiffOn ℝ k H c.source :=
    (contDiffOn_sourceMetricPairing g c.open_source hc (L v) (L w)).of_le
      (by exact_mod_cast le_top)
  have heq : (fun y => g.inner (affineChart c a L y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y w)) =ᶠ[𝓝 x]
      (fun y => g.inner (c (a + L y))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c (a + L y) (L v))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c (a + L y) (L w))) := by
    filter_upwards [(c.open_source.preimage
      (continuous_const.add L.continuous)).mem_nhds hx] with y hy
    have hcy := ((hc _ hy).contMDiffAt (c.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    rw [affineChart_mfderiv a L hcy v, affineChart_mfderiv a L hcy w, affineChart_apply]
  have hd := iteratedFDeriv_comp_affine (f := H) (k := k) c.open_source hH a
    (L : V →L[ℝ] A) hx
  exact (heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds.trans hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.iteratedFDeriv_affineChart_metricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.iteratedFDeriv_affineChart_metricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.iteratedFDeriv_affineChart_metricPairing ``Submission.DifferentialGeometry.Geometry.iteratedFDeriv_affineChart_metricPairing

end DifferentialGeometry.Geometry
