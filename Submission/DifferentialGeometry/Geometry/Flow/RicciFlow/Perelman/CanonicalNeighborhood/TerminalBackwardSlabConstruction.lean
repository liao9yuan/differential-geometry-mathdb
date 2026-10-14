import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardMetricLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactTimeComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_backward_extension_of_model_curvature_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    {sigma : ℝ} {Phi : ℝ → ℝ} (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨ef, hef, hflow⟩ := exists_backward_metric_limit_of_terminal_scalar_bound hmod
  obtain ⟨ec, hec, hbound⟩ := exists_eventually_curvature_bound_of_terminal_metric_scalar_le hmod
  refine ⟨min ef ec, lt_min hef hec, ?_⟩
  intro eps heps hle X L
  let P : MetricCompactLimit (X.toFlowSequence.atTime 0) := {
    subseq := L.subseq
    strictMono := L.strictMono
    limit := L.space
    limit_complete := L.complete
    maps := L.maps
    convergence := { metrics := L.converges } }
  obtain ⟨A, hA⟩ := L.scalar_bound
  obtain ⟨width, hw, hflowA⟩ :=
    hflow eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi A
  obtain ⟨depthBound, B, hdepth, hB, hcurv⟩ :=
    hbound eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi A
  obtain ⟨U, hUeq, hexhausts, _hcompact, N, F, hF, hsource, hmetric,
    rho, hrho, G, hG0, hG, hsec, hcomplete, hconv⟩ :=
    hflowA X P L.canonical_domains L.connected hA
  let delta := _root_.Min.min (width / 4) depthBound
  have hd : 0 < delta := lt_min (by positivity) hdepth
  have hdw : delta ≤ width / 4 := min_le_left _ _
  have hdc : delta ≤ depthBound := min_le_right _ _
  have hsub : _root_.Set.Icc (-delta) 0 ⊆ _root_.Set.Icc (-width / 2) 0 :=
    _root_.Set.Icc_subset_Icc (by linarith) le_rfl
  let D := RealTimeInterval.closed (-delta) 0 (by linarith : -delta ≤ 0)
  let S : SolutionOn (I := I3) (M := L.space.M) D := { base.metric := G }
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict hG hsub
    (_root_.Set.Ioo_subset_Ioo (by linarith) le_rfl)
  let C : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B
  have hC : 0 ≤ C := by positivity
  have hscalar : ∀ t ∈ _root_.Set.Icc (-delta) 0, ∀ y : L.space.M,
      |metricScalarAt (G t) y| ≤ C := by
    intro t ht y
    obtain ⟨n, hn⟩ := hexhausts.subset {y} isCompact_singleton
    have hyn : y ∈ U n := hn n le_rfl (_root_.Set.mem_singleton y)
    have hpU : P.limit.basepoint ∈ U n := by
      change P.limit.basepoint ∈ (U n : Set P.limit.M)
      rw [hUeq n]
      change riemannianEDistOf (I := I3) P.limit.metric P.limit.basepoint P.limit.basepoint < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    let f : ℕ → ℕ := fun i => P.subseq (rho i - N n + N n)
    let Psi (i : ℕ) := P.maps.partialDiffeomorph (rho i - N n + N n)
    obtain ⟨Q, hQmap, Qconv, hQcanonical⟩ :=
      exists_pointed_metric_convergence_of_pullback_on_open
        (X.toFlowSequence.atTime t) P.limit f Psi (U n) hpU
        (fun i => hsource n (rho i - N n))
        (fun i => P.maps.basepoint_map (rho i - N n + N n))
        (fun i => (F n (rho i - N n)).base.metric t)
        ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n))
        (fun i => hmetric n (rho i - N n) t) (by
          intro K hK p epsilon hepsilon
          obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
          exact ⟨j, fun i hi => hj i hi t (hsub ht)⟩)
    have htconv := (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      Qconv hQcanonical (⟨y, hyn⟩ : U n)).abs
    have hlimit : |metricScalarAt ((G t).restrictOpen (U n)) (⟨y, hyn⟩ : U n)| ≤ C := by
      apply le_of_tendsto htconv
      have hcurvy := hcurv X P.limit P.subseq P.strictMono P.maps P.convergence.metrics
        L.canonical_domains {y} isCompact_singleton (fun z _ => hA z)
      have hshift : _root_.Filter.Tendsto (fun i => rho i - N n + N n) _root_.Filter.atTop atTop := by
        apply hrho.tendsto_atTop.congr'
        filter_upwards [_root_.Filter.eventually_ge_atTop (N n)] with i hi
        exact (Nat.sub_add_cancel (hi.trans (hrho.id_le i))).symm
      filter_upwards [hshift.eventually hcurvy] with i hi
      rw [hQmap]
      dsimp only [f, Psi]
      have hrm := hi.2.2.2 t ⟨by linarith [ht.1], ht.2⟩ y (_root_.Set.mem_singleton y)
      have hrm' : Tensor0SBundle.normSq0S (I := I3)
          ((X.term (P.subseq (rho i - N n + N n))).S.base.metric t)
          (P.maps.partialDiffeomorph (rho i - N n + N n) y) 4
          (metricRm04At ((X.term (P.subseq (rho i - N n + N n))).S.base.metric t)
            (P.maps.partialDiffeomorph (rho i - N n + N n) y)) ≤ B := by
        exact (rmNormSq_eq_curvDerivNormSq X (P.subseq (rho i - N n + N n)) t
          (P.maps.partialDiffeomorph (rho i - N n + N n) y)).le.trans hrm
      exact (scalar_abs_le_rm ((X.term (P.subseq (rho i - N n + N n))).S.base.metric t)
        (P.maps.partialDiffeomorph (rho i - N n + N n) y)).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm') (by positivity))
    simpa only [metricScalarAt_restrictOpen] using hlimit
  have hrm : ∀ t ∈ _root_.Set.Icc (-delta) 0, ∀ y : L.space.M,
      FlowMetricBall.rmNormSq S t y ≤ 100 ^ 2 * C ^ 2 := by
    intro t ht y
    have hnonneg : metricAlgebraicCurvatureTensorAt (G t) y ∈
        algebraicCurvatureOperatorNonnegativeCone := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        (G t) y (by simp [ThreeSpace])).mpr
      intro v w
      have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
        funext i
        fin_cases i <;> simp [vec4]
      simpa only [_root_.MulZeroClass.zero_mul, metricRm04StandardAt_apply, hvec] using
        hsec t (hsub ht) y (_root_.Set.mem_univ _) v w
    have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      (G t) y (by simp [ThreeSpace]) hnonneg
    have hsquare : (metricScalarAt (G t) y) ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hscalar t ht y)
    exact hnorm.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  have hcompare : ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
      _root_.Set.Icc a b ⊆ _root_.Set.Icc (-delta) 0 → ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ i in _root_.Filter.atTop, K ⊆ (P.maps.partialDiffeomorph (rho i)).source ∧
          Nonempty (MetricComparisonOn G ((X.term (P.subseq (rho i))).S.base.metric)
            (P.maps.partialDiffeomorph (rho i)) K (_root_.Set.Icc a b) order epsilon) := by
    intro K hK a b hab htimes order epsilon hepsilon
    obtain ⟨n, hn⟩ := hexhausts.subset K hK
    have hKn : K ⊆ U n := hn n le_rfl
    let D' := RealTimeInterval.closed (-width / 2) 0 (by linarith : -width / 2 ≤ 0)
    let F' (i : ℕ) := (F n (rho i - N n)).timeRestrict D'
    have hF' (i : ℕ) : IsSolutionOn (F' i) := isSolutionOn_timeRestrict
      (hF n (rho i - N n)) (_root_.Set.Icc_subset_Icc (by linarith) le_rfl)
      (_root_.Set.Ioo_subset_Ioo (by linarith) le_rfl)
    have hconv' : ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
        ∀ eta : ℝ, 0 < eta → ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc (-width / 4) 0,
          metricDerivNormSupOn K p ((F' i).base.metric t)
            ((G t).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < eta := by
      intro K hK p eta heta
      obtain ⟨j, hj⟩ := hconv n K hK p eta heta
      exact ⟨j, fun i hi t ht => hj i hi t ⟨by linarith [ht.1], ht.2⟩⟩
    have hcomp (J : Set ℝ) (hJ : UniqueDiffOn ℝ J) (hJsub : J ⊆ _root_.Set.Icc (-width / 4) 0) :=
      eventually_metricComparisonOn_of_local_flow_convergence
        (U n) F' hF' ({ base.metric := G } : SolutionOn (I := I3) (M := L.space.M) D') hG
        (show -width / 2 < -width / 4 by linarith) (show -width / 4 < 0 by linarith)
        rfl Subset.rfl (P.limit.metric.restrictOpen (U n)) hconv'
        (fun i => (X.term (P.subseq (rho i - N n + N n))).S.base.metric)
        (fun i => P.maps.partialDiffeomorph (rho i - N n + N n))
        (fun i => hmetric n (rho i - N n)) hJ hJsub hK hKn order hepsilon
    have hcomp' : ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn G
          ((X.term (P.subseq (rho i - N n + N n))).S.base.metric)
          (P.maps.partialDiffeomorph (rho i - N n + N n)) K (_root_.Set.Icc a b) order epsilon) := by
      rcases lt_or_eq_of_le hab with hab' | rfl
      · exact hcomp _ (uniqueDiffOn_Icc hab')
          (htimes.trans (_root_.Set.Icc_subset_Icc (by linarith) le_rfl))
      · filter_upwards [hcomp (_root_.Set.Icc (-width / 4) 0)
          (uniqueDiffOn_Icc (by linarith)) Subset.rfl] with i hi
        obtain ⟨Ci⟩ := hi
        rw [_root_.Set.Icc_self]
        exact ⟨Ci.restrictTimeSingleton
          ((_root_.Set.Icc_subset_Icc (by linarith) le_rfl) (htimes (by simp))) hepsilon.le⟩
    filter_upwards [hcomp', _root_.Filter.eventually_ge_atTop (N n)] with i hi hiN
    have heq : rho i - N n + N n = rho i := Nat.sub_add_cancel (hiN.trans (hrho.id_le i))
    have hsrc := hsource n (rho i - N n)
    rw [heq] at hi hsrc
    exact ⟨hKn.trans hsrc, hi⟩
  refine ⟨delta, hd, ⟨{
    solution := S
    isSolution := hS
    terminal := hG0
    subseq := rho
    strictMono := hrho
    convergence := ?_
    complete := ?_
    nonnegative := fun t ht => hsec t (hsub ht)
    compact_time_bound := ?_ }⟩⟩
  · intro K hK a b hab htimes order epsilon hepsilon
    have htime := (X.depth_tendsto.comp
      (P.strictMono.tendsto_atTop.comp hrho.tendsto_atTop)).eventually_ge_atTop delta
    filter_upwards [hcompare K hK a b hab htimes order epsilon hepsilon, htime] with i hi hitime
    refine ⟨?_, hi.1, hi.2⟩
    intro t ht
    rw [X.carrier_eq]
    have htd := htimes ht
    change delta ≤ X.depth (L.subseq (rho i)) at hitime
    refine ⟨?_, htd.2⟩
    change -(2 * X.depth (L.subseq (rho i))) ≤ t
    linarith [htd.1, X.depth_pos (L.subseq (rho i))]
  · intro t ht
    exact (hcomplete t (hsub ht)).complete
  · intro a b _hab htimes
    exact ⟨100 ^ 2 * C ^ 2, fun t ht y => hrm t (htimes ht) y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_backward_extension_of_model_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_backward_extension_of_model_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_backward_extension_of_model_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_backward_extension_of_model_curvature_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
