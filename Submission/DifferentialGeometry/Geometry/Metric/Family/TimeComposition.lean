import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem MetricFamilySmoothOn.comp_time
    {D D' : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D'.regular) (hc : ContinuousOn f D'.carrier)
    (hreg : _root_.Set.MapsTo f D'.regular D.regular) (hcar : _root_.Set.MapsTo f D'.carrier D.carrier) :
    MetricFamilySmoothOn D' (g ∘ f) where
  coeff x X Y := (hg.coeff x X Y).comp hf hreg
  coeff_cont x X Y := (hg.coeff_cont x X Y).comp hc hcar
  metricTensor_cont := by
    have hmap : Continuous (fun q : D'.carrier × M =>
        ((⟨f q.1.1, hcar q.1.2⟩ : D.carrier), q.2)) :=
      ((hc.domRestrict.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    exact hg.metricTensor_cont.comp hmap
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    have ht : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => f p.1) (D'.regular ×ˢ u) :=
      hf.contMDiffOn.comp contMDiffOn_fst (fun p hp => hp.1)
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (f p.1, p.2)) (D'.regular ×ˢ u) :=
      ht.prodMk contMDiffOn_snd
    exact (hg.frameCompSmooth frame hframe i j).comp hmap (fun p hp => ⟨hreg hp.1, hp.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.comp_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.comp_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.comp_time ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.comp_time

end DifferentialGeometry.Geometry.Curvature
