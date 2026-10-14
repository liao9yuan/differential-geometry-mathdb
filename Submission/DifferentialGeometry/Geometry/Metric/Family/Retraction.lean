import Submission.DifferentialGeometry.Geometry.Metric.Retraction
import Submission.DifferentialGeometry.Geometry.Metric.Family.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Family.Stationary
import Submission.DifferentialGeometry.Geometry.Metric.Family.Product
import Submission.DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import Submission.DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Retraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricFamilySmoothOn_retractionMetric
    {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) :
    MetricFamilySmoothOn (I := 𝓘(ℝ, F)) (M := U) D
      (fun t => retractionMetric (g t) he hr) := by
  let hE : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) F :=
    fun _ => euclideanMetric (E := F)
  have hh : MetricFamilySmoothOn (I := 𝓘(ℝ, F)) (M := F) D hE := by
    simpa [hE, stationaryMetricFamily] using
      (metricFamilySmoothOn_stationary (I := 𝓘(ℝ, F)) (M := F)
        (euclideanMetric (E := F)) D)
  have hp : MetricFamilySmoothOn (I := I.prod 𝓘(ℝ, F)) (M := M × F) D
      (fun t => (g t).prod (euclideanMetric (E := F))) :=
    MetricFamilySmoothOn.prod hg hh
  have hpull := hp.of_pullback
      (fun t => retractionMetric (g t) he hr)
      (fun x : U => retractionGraph e r x)
      (contMDiff_retractionGraph he hr)
      (by
        intro t x v w
        rfl)
  exact hpull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_retractionMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_retractionMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_retractionMetric ``Submission.DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_retractionMetric

theorem exists_metricFamilySmoothOn_totally_geodesic_extension [I.Boundaryless] [CompactSpace M] [Nonempty M]
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (U : TopologicalSpace.Opens F) (hEU : Set.range e ⊆ U)
      (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U),
      MetricFamilySmoothOn (I := 𝓘(ℝ, F)) (M := U) D G ∧
      (∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (G t).inner ⟨e p, hEU (Set.mem_range_self p)⟩
          (mfderiv I 𝓘(ℝ, F) e p v) (mfderiv I 𝓘(ℝ, F) e p w) = (g t).inner p v w) ∧
      ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t)
        (fun p : M => (⟨e p, hEU (Set.mem_range_self p)⟩ : U)) := by
  obtain ⟨r, V, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  let U : TopologicalSpace.Opens F := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, F) I ∞ r U := hr
  refine ⟨U, heV, fun t => retractionMetric (g t) he hrU,
    metricFamilySmoothOn_retractionMetric g hg he hrU, ?_, ?_⟩
  · intro t p v w
    exact retractionMetric_inner_map (g t) he hrU heV hleft p v w
  · intro t
    exact hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
      (g t) he hrU heV hleft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_totally_geodesic_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_totally_geodesic_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_totally_geodesic_extension ``Submission.DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_totally_geodesic_extension

theorem exists_metricFamilySmoothOn_extension [I.Boundaryless] [CompactSpace M] [Nonempty M]
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (U : TopologicalSpace.Opens F) (hEU : Set.range e ⊆ U)
      (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U),
      MetricFamilySmoothOn (I := 𝓘(ℝ, F)) (M := U) D G ∧
      ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (G t).inner ⟨e p, hEU (Set.mem_range_self p)⟩
          (mfderiv I 𝓘(ℝ, F) e p v) (mfderiv I 𝓘(ℝ, F) e p w) = (g t).inner p v w := by
  obtain ⟨U, hEU, G, hG, hinner, _⟩ :=
    exists_metricFamilySmoothOn_totally_geodesic_extension g hg he hemb hi
  exact ⟨U, hEU, G, hG, hinner⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_extension ``Submission.DifferentialGeometry.Geometry.Curvature.exists_metricFamilySmoothOn_extension

end DifferentialGeometry.Geometry.Curvature
