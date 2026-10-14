import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Extraction
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.SourceMetricConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_finite_pointed_metric_comparison_of_local_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in _root_.Filter.atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in _root_.Filter.atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ C : ChartedSpace E Q, letI := C
      ∃ hman : IsManifold (modelWithCornersSelf ℝ E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) Q)
        (V U : TopologicalSpace.Opens Q) (q : Q)
        (F : ∀ k, Q → (X.obj (phi k)).M)
        (G : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) U),
        IsCompact (closure (V : Set Q)) ∧ closure (V : Set Q) ⊆ U ∧ q ∈ V ∧
        (∀ᶠ k in _root_.Filter.atTop, ∀ (x : U) (v w : TangentSpace (modelWithCornersSelf ℝ E) x),
          (G k).inner x v w = (X.obj (phi k)).metric.inner (F k x)
            (mfderiv (modelWithCornersSelf ℝ E) I (F k) (x : Q) v)
            (mfderiv (modelWithCornersSelf ℝ E) I (F k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen U) (gQ.restrictOpen U) ∧
        ∀ᶠ k in _root_.Filter.atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I Q (X.obj (phi k)).M ∞,
          closure (U : Set Q) ⊆ Φ.source ∧ _root_.Set.EqOn Φ (F k) Φ.source ∧
          Φ q = (X.obj (phi k)).basepoint ∧
          (∀ y : (X.obj (phi k)).M,
            riemannianEDistOf (I := I) (X.obj (phi k)).metric
              (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r →
            y ∈ Φ '' (V : Set Q)) ∧
          Φ '' closure (V : Set Q) ⊆
            {y | riemannianEDistOf (I := I) (X.obj (phi k)).metric
              (X.obj (phi k)).basepoint y < ENNReal.ofReal R} := by
  classical
  let : ∀ k, _root_.Bundle.RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle (I := I)
  let : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun k => (X.obj k).riemInner (I := I)
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle_cont (I := I)
  let : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
  let : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
  let : ∀ k, CompleteSpace (X.obj k).M :=
    fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let hEnorm : ∀ k (x : (X.obj k).M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner x v v)) := by
    intro k x v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric x v
  obtain ⟨ρ, hρ, hρR, N, phi, hphi, c, charts, B, near, hclass, J, hcont, hconv,
    hbase, hc, hcover, hell, hmetric, htrans, C, hman, hchart, gQ, hgQ,
    U, W, hU, hW, hKU, hUW, F, hFsmooth, hFbase, hFconv, hFtarget, hPhi⟩ :=
      exists_finite_pointed_source_partialDiffeomorphs_of_local_curvature_injectivity
        X hcomplete hconn hr hrR hη hjets hinj
  let D := IntrinsicBallChart.bufferedTransitionGlueData
    (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts near hclass J hcont hconv
  let A : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
  let := C
  let := hman
  let ht2 : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space
      (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k))
      c hρ charts near hclass J hcont hconv
  let hsecond : SecondCountableTopology D.toGlueData.glued := by
    let : Countable D.J := by
      change Countable (ULift.{uE} (Fin (N + 1)))
      infer_instance
    let : ∀ i : D.J, SecondCountableTopology (D.U i) := by
      intro i
      change SecondCountableTopology (Metric.ball (0 : E) (ρ / 8))
      infer_instance
    exact TopCat.GlueData.secondCountableTopology D
  let : LocallyCompactSpace D.toGlueData.glued :=
    ChartedSpace.locallyCompactSpace E D.toGlueData.glued
  have hK := IntrinsicBallChart.isCompact_transitionGlueCompactCore
    (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts near hclass J hcont hconv
  have hpK := (IntrinsicBallChart.transitionGlueCore_subset_compactCore
    (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts near hclass J hcont hconv)
      (IntrinsicBallChart.zero_mem_transitionGlueCore
        (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts near hclass J hcont hconv
        (ULift.up 0))
  obtain ⟨Vset, hVopen, hKV, hVU, hV⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  let V : TopologicalSpace.Opens D.toGlueData.glued := ⟨Vset, hVopen⟩
  have hUsubsetW : (U : Set D.toGlueData.glued) ⊆ W := subset_closure.trans hUW
  have hVsubsetW : (V : Set D.toGlueData.glued) ⊆ W :=
    subset_closure.trans (hVU.trans hUsubsetW)
  have hpartial : ∀ᶠ k in _root_.Filter.atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I
      D.toGlueData.glued (X.obj (phi k)).M ∞,
      (U : Set D.toGlueData.glued) ⊆ Φ.source ∧ _root_.Set.EqOn Φ (F k) Φ.source := by
    filter_upwards [hPhi] with k hk
    obtain ⟨Φ, hUΦ, _, hΦF, _⟩ := hk
    exact ⟨Φ, subset_closure.trans hUΦ, hΦF⟩
  obtain ⟨G, hG, hGconv⟩ := IntrinsicBallChart.exists_metricCInfConvergenceOnCompacts_of_chart_convergence
    (fun _ : ULift.{uE} (Fin (N + 1)) => A)
    (fun _ => Metric.ball_subset_ball (by linarith : ρ / 8 ≤ ρ))
    (fun i (z : A) => D.toGlueData.ι i z) hchart
    (fun i => (D.ι_isOpenEmbedding i).injective) U
    (fun x => D.ι_jointly_surjective (x : D.toGlueData.glued))
    (fun k => (X.obj (phi k)).metric) gQ (fun k => hEnorm (phi k)) c charts F
    B
    (fun i => (hmetric i).2.1) (fun i => (hmetric i).1) hgQ
    (fun i L hL hLU => hFtarget i L hL
      (hLU.trans (_root_.Set.image_mono (_root_.Set.preimage_mono hUsubsetW))))
    (fun i L hL hLU p => hFconv i L hL
      (hLU.trans (_root_.Set.image_mono (_root_.Set.preimage_mono hUsubsetW))) p) hpartial
  have hcapture := IntrinsicBallChart.eventually_chart_core_subset_image
    (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts near hclass J hcont hconv
    C (fun i => (hchart i).contMDiff) V hKV F
    (Eventually.of_forall fun k => (hFsmooth k).mono hVsubsetW)
    (fun i L hL hLV p => hFconv i L hL
      (hLV.trans (_root_.Set.image_mono (_root_.Set.preimage_mono hVsubsetW))) p)
    (fun i L hL hLV => hFtarget i L hL
      (hLV.trans (_root_.Set.image_mono (_root_.Set.preimage_mono hVsubsetW))))
  refine ⟨phi, hphi, D.toGlueData.glued, inferInstance, C, hman, ht2, hsecond, gQ, V, U,
    D.toGlueData.ι (ULift.up 0) ⟨0, Metric.mem_ball_self (by positivity)⟩,
    F, G, hV, hVU, hKV hpK, hG.mono (fun _ hk => hk.2), hGconv, ?_⟩
  filter_upwards [hPhi, hcapture] with k hk hcap
  obtain ⟨Φ, hUΦ, _, hΦF, hΦbase, _, hupper⟩ := hk
  have hVΦ : closure (V : Set D.toGlueData.glued) ⊆ Φ.source :=
    hVU.trans (subset_closure.trans hUΦ)
  refine ⟨Φ, hUΦ, hΦF, hΦbase, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, z, hz, rfl⟩ := hcover k y hy
    obtain ⟨q, hqV, hqeq⟩ := hcap i ⟨z, Metric.ball_subset_closedBall hz, rfl⟩
    exact ⟨q, hqV, (hΦF (hVΦ (subset_closure hqV))).trans hqeq⟩
  · intro y hy
    change _root_.EDist.edist (X.obj (phi k)).basepoint y < ENNReal.ofReal R
    rw [_root_.PseudoEMetricSpace.edist_comm]
    exact hupper ((_root_.Set.image_mono (hVU.trans subset_closure)) hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_finite_pointed_metric_comparison_of_local_curvature_injectivity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_finite_pointed_metric_comparison_of_local_curvature_injectivity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_finite_pointed_metric_comparison_of_local_curvature_injectivity ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_finite_pointed_metric_comparison_of_local_curvature_injectivity

end DifferentialGeometry.CheegerGromovCompactness

end

end
