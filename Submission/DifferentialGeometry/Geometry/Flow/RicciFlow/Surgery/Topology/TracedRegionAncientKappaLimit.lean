import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitScalarBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLimitOrientation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitBaseScalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood (ancientTimeInterval IsAncientKappaSolution
  PointedFlowScalarAtBase)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness
  isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative)

open private ObservedHistory.mem_Icc_of_mem_window from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_ancientKappa_pointed_limit_of_isTracedRegion :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, _root_.Set.Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
    (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
    _root_.Filter.Tendsto R _root_.Filter.atTop _root_.Filter.atTop →
    (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in _root_.Filter.atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
    ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ {t₀ : ℕ → ℝ},
    _root_.Filter.Tendsto (fun n => R n * (t n - t₀ n)) _root_.Filter.atTop (𝓝 0) →
    (∀ n (v : _root_.Set.Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r)) →
    ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
    (∀ n (v : _root_.Set.Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
      ∀ x : ((H n).stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) →
    ∀ {eps C1 C2 Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ}, 0 < eps → eps ≤ epsW →
    (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
    (∀ n (v : _root_.Set.Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 p,
          Wt.capTubeHasNeckChart eps) →
    (∀ n (v : _root_.Set.Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
          (_root_.Set.Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X P f),
        (∃ C : MetricConvergenceData F,
          ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧ Nonempty (TangentOrientationSection P.M) ∧
        ∃ (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
          (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
            ancientTimeInterval)),
          G 0 = P.metric ∧
          IsAncientKappaSolution (κ / 250 / 30 ^ 3)
            (flowOfMetric ancientTimeInterval P G hG) ∧
          PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1 := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}
  refine ⟨epsW, hepsW, ?_⟩
  intro H t y R hR hscal hRlim htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch eps C1 C2 Cs Cq
    Ctime qs qcan heps hepsW' hqs hqcan hwit hderiv X
  obtain ⟨W, h, hblock, -, -, -, f, hf, P, F, hC, hPc, hconn, -, V, N, hV, hVF, φ, hφ, hφF, G,
    hG0, hG, ψ, hψ, hconv, hκG, CB, hCB⟩ :=
    hB13 H t y R hR hRlim htraced hκ hρ hsliver hnc hPhi hpinch heps hepsW' hqs hqcan hwit hderiv
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in _root_.Filter.atTop, ∀ q ∈ _root_.Set.Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hblock k] with n hn q hq x
    obtain ⟨-, -, -, ⟨a, -, ha, fs, hfs, -, -, -, hp⟩, -⟩ := hn
    have hqθ : q ∈ _root_.Set.Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : _root_.Set.Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono (show a ≤ v from hv.1),
        (H n).activeStage_mono (show v ≤ t n from hv.2)⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (fs j) (hfs j) x _).mpr
      (hpinch n v hv.2 (fs j x))
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      metricScalarAt_localPull]
    unfold Perelman.rescalePinchingFunction
    simp only [mul_inv_cancel_left₀ (hR n).ne']
    exact hpull
  obtain ⟨hcone, hcomplete⟩ := ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    hf hPc hconn hV hG0 hG hψ hconv hRlim hPhi hpinchW
  have hbaseP : metricScalarAt P.metric P.basepoint = 1 := by
    refine metricScalarAt_basepoint_eq_of_local_flow_limit hf F hV hφF hG0 hψ hconv ?_ ?_
    · intro k
      filter_upwards [hblock k] with n hn z
      have hdom0 : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
        simpa using (H n).activeStage_mem (t n)
      rw [hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0, zero_div, add_zero,
        metricScalarAt_scaleMetric, metricScalarAt_restrictOpen]
      exact (metricScalarAt_scaleMetric (R n) (hR n) _ _).symm
    · intro n
      change metricScalarAt (scaleMetric (R n) (hR n)
        ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
      rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  have ho := haveI := hconn
    nonempty_tangentOrientationSection_of_pointedConvergence F
      (fun n => ((H n).stageAt (t n)).orientation) hV hVF
  obtain ⟨hanc, hbase⟩ := isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative
    P hG hG0 hconn hcomplete hcone hCB (div_pos hκ (by norm_num)) hκG hbaseP
  exact ⟨f, hf, P, F, hC, hPc, hconn, ho, G, hG, hG0, hanc, hbase⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_ancientKappa_pointed_limit_of_isTracedRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_ancientKappa_pointed_limit_of_isTracedRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_ancientKappa_pointed_limit_of_isTracedRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_ancientKappa_pointed_limit_of_isTracedRegion

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
