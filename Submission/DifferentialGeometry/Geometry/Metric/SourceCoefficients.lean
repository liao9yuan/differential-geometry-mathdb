import Submission.DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.CompactBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem contDiffOn_sourceMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U) (v w : V) :
    ContDiffOn ℝ ∞ (fun x => g.inner (f x)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x w)) U :=
  contDiffOn_sourceSectionPairing g hf
    (contMDiffOn_source_partial hU hf (by simp) v)
    (contMDiffOn_source_partial hU hf (by simp) w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_sourceMetricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_sourceMetricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_sourceMetricPairing ``Submission.DifferentialGeometry.Geometry.contDiffOn_sourceMetricPairing



theorem exists_bound_iteratedFDeriv_sourceMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v w : V) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun y => g.inner (f y)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y v) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y w)) x‖ ≤ C :=
  DifferentialGeometry.Analysis.exists_bound_iteratedFDeriv_on_compact hU
    (contDiffOn_sourceMetricPairing g hU hf v w) hK hKU k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_bound_iteratedFDeriv_sourceMetricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_bound_iteratedFDeriv_sourceMetricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_bound_iteratedFDeriv_sourceMetricPairing ``Submission.DifferentialGeometry.Geometry.exists_bound_iteratedFDeriv_sourceMetricPairing

end DifferentialGeometry.Geometry
