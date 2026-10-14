import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedExtensionMetricBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.LocalWindow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPointedChartControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_pointed_extension_metric_bounds_on_compact
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval) (hcomplete : FlowMetricComplete X)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} [ConnectedSpace P.M]
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hPcomplete : MetricComplete P)
    (G : ℕ → ℝ → SmoothRiemannianMetric I P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ F.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w))
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ᶠ i in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc (-T) 0, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A → (X.term i).rmNormSq t x ≤ Q)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc (-T) 0, ∀ x : (X.term i).M,
        ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∀ p : ℕ, ∀ K : Set P.M, IsCompact K →
      ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in _root_.Filter.atTop,
        (∀ q ≤ p, ∀ t ∈ _root_.Set.Icc (-T) 0, ∀ x ∈ K,
          metricCovDerivNorm q (G i t) P.metric x ≤ C) ∧
        (∀ q ≤ p, ∀ s ∈ _root_.Set.Icc (-T) 0, ∀ t ∈ _root_.Set.Icc (-T) 0, ∀ x ∈ K,
          metricDerivNorm q (G i s) (G i t) P.metric x ≤ L * |s - t|) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro T hT p K hK
  have hP : RiemannianMetricComplete P.metric := ⟨MetricComplete.complete P hPcomplete⟩
  obtain ⟨V, hKV, _hVc, A, hA, hVA⟩ :=
    exists_precompact_bounded_comparison_open P.metric hP P.basepoint hK
  have hKA := hKV.trans hVA
  have hcar : _root_.Set.Icc (-T) 0 ⊆ X.D.carrier := by
    rw [hD, ancientTimeInterval_carrier]
    exact _root_.Set.Icc_subset_Iic_self
  have hreg : _root_.Set.Ico (-T) 0 ⊆ X.D.regular := by
    rw [hD, ancientTimeInterval_regular]
    exact _root_.Set.Ico_subset_Iio_self
  have hjet := exists_eventually_curvDerivNorm_le_on_window_of_local_curvature_bound
    X hD hcomplete hlocal hlower
  obtain ⟨C₀, L, hC₀, hL, hbound⟩ := exists_eventually_pointed_extension_metric_bounds
    hphi F C hcanonical hPcomplete G hG (neg_neg_of_pos hT) hcar hreg p
    (fun R hR q _ => hjet R hR T hT q) hA.le
  refine ⟨C₀, L, hC₀, hL, hbound.mono fun i hi => ?_⟩
  exact ⟨fun q hq t ht x hx => hi.1 q hq t ht x (hKA hx),
    fun q hq s hs t ht x hx => hi.2 q hq s hs t ht x (hKA hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_pointed_extension_metric_bounds_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_pointed_extension_metric_bounds_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_pointed_extension_metric_bounds_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_pointed_extension_metric_bounds_on_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
