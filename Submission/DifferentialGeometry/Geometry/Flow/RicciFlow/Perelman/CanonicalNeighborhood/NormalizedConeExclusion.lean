import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaledLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular target :: scope.openDecls } }

private theorem intrinsic_end_cone_solution_exclusion
    (L : PointedRiemannianManifold.{u, 0, 0} I3)
    (W : TopologicalSpace.Opens L.M) (hW : PathConnectedSpace W) :
    let _ : PathConnectedSpace W := hW
    let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (q0 : UniformSpace.Completion W) (d : ℝ)
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d)
    (x : ℕ → W) (j : ℕ → ℕ) (hj : StrictMono j) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hQ : _root_.Filter.Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop _root_.Filter.atTop)
    (hratio : _root_.Filter.Tendsto (fun n => A n / metricScalarAt L.metric (x (j n) : L.M)) _root_.Filter.atTop (𝓝 1))
    (hlower : ∀ᶠ n in _root_.Filter.atTop, 196 < metricScalarAt L.metric (x n : L.M) * _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2)
    (hupper : ∃ B : ℝ, ∀ᶠ n in _root_.Filter.atTop, metricScalarAt L.metric (x n : L.M) * _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B)
    (P : PointedRiemannianManifold.{0, 0, 0} I3) (hpath : PathConnectedSpace P.M)
    (tau : ℝ) (htau : 0 < tau)
    (S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    (C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞) (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = P.metric)
    (hsec : ∀ t ∈ _root_.Set.Icc (-tau) 0, SecLower (S.base.metric t) 0 _root_.Set.univ)
    (hscalar : metricScalarAt P.metric P.basepoint = 1)
    (hbase : ∀ n, C n P.basepoint = x (j n))
    (r : ℝ) (hr : 0 < r) (hK : IsCompact (riemannianClosedBallOf P.metric P.basepoint r)),
    (∀ᶠ n in _root_.Filter.atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
      riemannianClosedBallOf (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (x (j n)) (r / 4) ⊆
        (C n) '' riemannianClosedBallOf P.metric P.basepoint r) →
    (∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
      ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
      ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
        |metricDistance (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (C n a) (C n b) -
          metricDistance P.metric a b| < eta) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro q0 d cone x j hj A hA hQ hratio hlower hupper P hpath tau htau S C hS hterminal
    hsec hscalar hbase r hr hK hcapture hdist
  exact rescaled_end_cone_exclusion (L.metric.restrictOpen W) (fun _ _ => rfl)
    cone x j hj A hA (fun n => metricScalarAt L.metric (x n : L.M))
    hQ hratio (c := 196) (by norm_num) (hlower.mono fun _ h => h.le)
    hupper P hpath tau htau S (fun n a => C n a) hS hterminal
    hsec (by rw [hscalar]; norm_num) hbase r hr hK (hcapture.mono fun _ h => h.2) hdist

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.intrinsic_end_cone_solution_exclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.intrinsic_end_cone_solution_exclusion target :: scope.openDecls } }

theorem normalized_end_cone_exclusion {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      ∀ f : ℕ → ℕ, StrictMono f →
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
        ∀ y ∈ maps.source i, ∀ v : TangentSpace I3 y,
          (1 - eta) * L.metric.inner y v v ≤
            ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ∧
          ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ≤
            (1 + eta) * L.metric.inner y v v) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∀ q0 : UniformSpace.Completion W, ∀ d : ℝ, 0 < d →
        IsCompact (Metric.closedBall q0 d) →
        Metric.closedBall q0 d ⊆ _root_.Insert.insert q0 (_root_.Set.range (fun x : W => (x : UniformSpace.Completion W))) →
      ∀ x : ℕ → W, _root_.Filter.Tendsto (fun n => (x n : UniformSpace.Completion W)) _root_.Filter.atTop (𝓝 q0) →
        _root_.Filter.Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop _root_.Filter.atTop →
        (∀ᶠ n in _root_.Filter.atTop, 196 < metricScalarAt L.metric (x n : L.M) *
          _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2) →
        (∃ B : ℝ, ∀ᶠ n in _root_.Filter.atTop, metricScalarAt L.metric (x n : L.M) *
          _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B) →
        Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d) → False := by
  obtain ⟨epsStar, hepsStar, hproduce⟩ := exists_local_backward_limit_on_normalized_end.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp W hW
    instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro q0 d hd hKd hcover x hx hQ hlower hupper hcone
  as_aux_lemma =>
    obtain ⟨cone⟩ := hcone
    obtain ⟨j, k, hj, _, hq, hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec,
      hscalar, hbase, r, hr, hK, hcapture, hdist⟩ :=
      hproduce eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp
        W hW q0 d hd hKd hcover x hx hQ hlower
    as_aux_lemma =>
      clear hproduce
      let A := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      have hA (n : ℕ) : 0 < A n := lt_of_lt_of_le zero_lt_one (hq n)
      change _root_.Filter.Tendsto (fun n => A n / metricScalarAt L.metric (x (j n) : L.M)) _root_.Filter.atTop (𝓝 1) at hratio
      change (∀ᶠ n in _root_.Filter.atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
        riemannianClosedBallOf (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (x (j n)) (r / 4) ⊆
          (C n) '' riemannianClosedBallOf P.metric P.basepoint r) at hcapture
      change (∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
        ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
        ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
          |metricDistance (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (C n a) (C n b) -
            metricDistance P.metric a b| < eta) at hdist
      generalize hdef : A = A' at hA hratio hcapture hdist
      clear hdef hq A
      as_aux_lemma =>
        exact intrinsic_end_cone_solution_exclusion L W hW q0 d cone x j hj A' hA
          hQ hratio hlower hupper P hpath tau htau S C hS hterminal hsec hscalar hbase r hr hK
          hcapture hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.normalized_end_cone_exclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.normalized_end_cone_exclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.normalized_end_cone_exclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.normalized_end_cone_exclusion

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
