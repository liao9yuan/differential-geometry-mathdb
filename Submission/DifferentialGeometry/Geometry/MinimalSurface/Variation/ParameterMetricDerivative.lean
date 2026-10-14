import Submission.DifferentialGeometry.Geometry.Metric.FamilySourceDerivative
import Submission.DifferentialGeometry.Geometry.Connection.SourceCovariantPartial
import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem hasDerivAt_parameterMetricPartial
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {F : ℝ × A → M} {s : Set (ℝ × A)} (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) ∞ F s)
    {z : A} (hz : (t, z) ∈ s) (v : A) :
    let V := fun p => mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F p (0, v)
    let W := fun q => mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, q) (1, 0)
    HasDerivAt (fun r => (G r).inner (F (r, z)) (V (r, z)) (V (r, z)))
      (deriv (fun r => (G r).inner (F (t, z)) (V (t, z)) (V (t, z))) t +
        2 * (G t).inner (F (t, z))
          (sourceSectionCovariantDerivative (G t) (fun q => F (t, q)) W z v) (V (t, z))) t := by
  dsimp only
  have hv := contMDiffOn_source_partial hs hF (m := ∞) (by simp) (0, v)
  have hc : ContDiffAt ℝ ∞ (fun r : ℝ => (r, z)) t :=
    contDiffAt_id.prodMk contDiffAt_const
  have hd := hasDerivAt_metricFamilySourcePairing hG ht hs hF hv hv hc hz
  have hcderiv : deriv (fun r : ℝ => (r, z)) t = (1, 0) := by
    exact ((hasDerivAt_id t).prodMk (hasDerivAt_const t z)).deriv
  rw [hcderiv] at hd
  change HasDerivAt _
    (deriv _ t +
      (G t).inner (F (t, z)) (sourceCovariantPartial (G t) F (t, z) (1, 0) (0, v)) _ +
      (G t).inner (F (t, z)) _ (sourceCovariantPartial (G t) F (t, z) (1, 0) (0, v))) t at hd
  rw [sourceCovariantPartial_symm (G t) hs hF hz (1, 0) (0, v)] at hd
  simp only [sourceCovariantPartial, sourceSectionCovariantDerivative_parameter_slice] at hd
  rw [(G t).symm (F (t, z))
    (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, z) (0, v))] at hd
  convert hd using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivAt_parameterMetricPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivAt_parameterMetricPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivAt_parameterMetricPartial ``Submission.DifferentialGeometry.Geometry.hasDerivAt_parameterMetricPartial

end DifferentialGeometry.Geometry
