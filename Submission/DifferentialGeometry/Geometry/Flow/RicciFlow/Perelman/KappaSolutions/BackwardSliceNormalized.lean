import Submission.DifferentialGeometry.Geometry.Curvature.ModelChange
import Submission.DifferentialGeometry.Geometry.Operator.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassNaturality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowNormalized
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricJetScaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalPoleCenters
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
universe u uE uH
section EuclideanModel
variable {n : ℕ} {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem exists_backward_slice_normalized_shrinker_of_euclidean_model
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (P : PointedRiemannianManifold.{u, 0, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
        (C : MetricConvergenceData Psi),
        (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i) ∧
        (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        (∀ x : P.M, 0 < metricScalarAt P.metric x) ∧
        (∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        ∃ f : C^∞⟮I, P.M; ℝ⟯,
          Geometry.normalizedGradientRicciSoliton P.metric f ∧
          normalizedShrinkerMass P.metric f = asymptoticReducedVolume F.S 0 p ∧
          ∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
            (fun i x => redLength F.S 0 p (Psi.map i x) (tau (phi i))) f _root_.Filter.atTop K := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := neZero_finrank_of_isAncientKappaSolution F hF
  let sigma := fun i => tau i / 2
  have hsigma (i : ℕ) : 0 < sigma i := half_pos (htau i)
  have hsbase (i : ℕ) : redLength F.S 0 p (q i) (sigma i) ≤
      2 * (1 + Real.sqrt 3) ^ 2 * A := by
    have h := redLength_le_of_backward_time_le F hF p (q i)
      (s := tau i / 2) (hsigma i) (by linarith [htau i]) (hbase i)
    have heq : tau i / (tau i / 2) = 2 := by field_simp [(htau i).ne']
    simpa only [sigma, heq, mul_comm ((1 + Real.sqrt 3) ^ 2) 2] using h
  have hses : _root_.Filter.Tendsto sigma _root_.Filter.atTop atTop := hescape.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, R, G, hG, hmetric,
    ell, _hnonneg, _hellbase, hLip, hell⟩ :=
    exists_backward_flow_reducedLength_limit_with_uniform_metric_convergence
      F hF p sigma hsigma q hsbase (T := 3) (by norm_num)
  let _ : ConnectedSpace L.M := hconn
  have hconv' (t : ℝ) (ht : t ∈ _root_.Set.Icc (1 - 3) (0 : ℝ)) :=
    (hconv t ht.2).imp (fun C hC => hC.1)
  have hcomp' (t : ℝ) (ht : t ∈ _root_.Set.Icc (1 - 3) (0 : ℝ)) := hcomp t ht.2
  have hsescape := hses.comp hphi.tendsto_atTop
  obtain ⟨hf, hsol, hmass⟩ := backward_flow_reducedLength_limit_normalized_shrinker_and_mass
    F hF p sigma hsigma q L Phi R G hG hmetric (by norm_num : (1 : ℝ) < 3)
    ell hell hLip hsescape hconv' hcomp' (t := 2) (by norm_num)
  have hpos := backward_flow_reducedLength_limit_scalar_pos
    F hF p sigma hsigma q L Phi R G hG hmetric (by norm_num : (1 : ℝ) < 3)
    ell hell hLip hsescape hconv' hcomp' (t := 2) (by norm_num)
  let P : PointedRiemannianManifold.{u, 0, uH} (I := I) :=
    { L.atTime (-1) with metric := scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)) }
  let Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi := {
    partialDiffeomorph := Phi.partialDiffeomorph
    source_exhausts := Phi.source_exhausts
    base_mem := Phi.base_mem
    basepoint_map := Phi.basepoint_map }
  have hmetric' : MetricCInfConvergenceOnCompacts (fun i => G i (-1))
      (L.S.base.metric (-1)) R := by
    intro K hK r epsilon hepsilon
    obtain ⟨N, hN⟩ := hmetric (-1) (-1) (fun _ ht => ht.2.trans (by norm_num)) K hK r epsilon hepsilon
    exact ⟨N, fun i hi => hN i hi (-1) ⟨le_rfl, le_rfl⟩⟩
  let GS := fun i => scaleMetric (2 : ℝ)⁻¹ (by norm_num) (G i (-1))
  have hscaled : MetricCInfConvergenceOnCompacts GS P.metric P.metric :=
    (metricCInfConvOnCompacts_scale_all (2 : ℝ)⁻¹ (by norm_num)
      (fun i => G i (-1)) (L.S.base.metric (-1)) R hmetric').change_reference P.metric
  have hscaledG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Psi.source i ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (GS i).inner x v w = ((backwardSliceSequence F tau htau q).obj (phi i)).metric.inner
            (Psi.map i x) (mfderiv I I (Psi.map i) x v) (mfderiv I I (Psi.map i) x w) := by
    intro K hK
    filter_upwards [hG K hK] with i hi
    obtain ⟨U, hU, hKU, hUsrc, hGi⟩ := hi
    refine ⟨U, hU, hKU, hUsrc, ?_⟩
    intro x hx v w
    change (2 : ℝ)⁻¹ * (G i (-1)).inner x v w = _
    rw [hGi (-1) x hx v w, backwardFlowSequence_metric]
    have htime : sigma (phi i) * ((-1 : ℝ) - 1) = -tau (phi i) := by dsimp [sigma]; ring
    rw [htime]
    change (2 : ℝ)⁻¹ * ((sigma (phi i))⁻¹ *
      (F.S.base.metric (-tau (phi i))).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) =
      (tau (phi i))⁻¹ * (F.S.base.metric (-tau (phi i))).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)
    dsimp only [sigma]
    field_simp
  obtain ⟨C, hcanonical, href⟩ :=
    exists_canonicalMetricConvergenceData_of_metric_extension Psi GS hscaled hscaledG
  have hcone : ∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone := by
    apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence C hcanonical
    intro K _hK
    filter_upwards [] with i
    intro y _hy _hysrc
    change metricAlgebraicCurvatureTensorAt
      (scaleMetric (tau (phi i))⁻¹ (inv_pos.mpr (htau _))
        (F.S.base.metric (-tau (phi i)))) (Psi.map i y) ∈ _
    rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
    apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr (htau _)).le
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff _ _).mpr
    intro m c v w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-tau (phi i)) (neg_nonpos.mpr (htau _).le)
        (Psi.map i y) m c v w
  have hcomplete : MetricComplete P := by
    have hc : RiemannianMetricComplete (L.S.base.metric (-1)) := ⟨hcomp (-1) (by norm_num)⟩
    exact (hc.of_lower (by norm_num : (0 : ℝ) < 2⁻¹) (fun _ _ => le_rfl)).complete
  refine ⟨P, phi, hphi, Psi, C, hcanonical, href, hcomplete, hconn, ?_, hcone,
    ⟨fun x => ell (x, _root_.Set.projIcc 1 3 (by norm_num) 2), hf⟩, ?_, ?_, ?_⟩
  · intro x
    change L.M at x
    change 0 < metricScalarAt (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1))) x
    rw [metricScalarAt_scaleMetric, inv_inv]
    exact mul_pos (by norm_num) (by simpa only [show (1 : ℝ) - 2 = -1 by norm_num] using hpos x)
  · change Geometry.normalizedGradientRicciSoliton
      (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)))
      ⟨fun x => ell (x, _root_.Set.projIcc 1 3 (by norm_num) 2), hf⟩
    convert hsol using 1
    norm_num
  · change normalizedShrinkerMass
      (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)))
      (fun x => ell (x, _root_.Set.projIcc 1 3 (by norm_num) 2)) = _
    convert hmass using 1
    norm_num
  · intro K hK
    let theta : _root_.Set.Icc (1 : ℝ) 3 := ⟨2, by norm_num, by norm_num⟩
    have hc : Continuous (fun x : P.M => (x, theta)) := continuous_id.prodMk continuous_const
    have h := (hell ((fun x : P.M => (x, theta)) '' K) (hK.image hc)).comp (fun x : P.M => (x, theta))
    have h' := h.mono (show K ⊆ (fun x : P.M => (x, theta)) ⁻¹'
      ((fun x : P.M => (x, theta)) '' K) from fun x hx => _root_.Set.mem_image_of_mem _ hx)
    have hscale (i : ℕ) : sigma (phi i) * (theta : ℝ) = tau (phi i) := by dsimp [sigma, theta]; ring
    change TendstoUniformlyOn
      (fun i x => redLength F.S 0 p (Phi.map i x) (tau (phi i)))
      (fun x => ell (x, _root_.Set.projIcc 1 3 (by norm_num) 2)) _root_.Filter.atTop K
    rw [_root_.Set.projIcc_of_mem (by norm_num : (1 : ℝ) ≤ 3) (show (2 : ℝ) ∈ _root_.Set.Icc 1 3 by norm_num)]
    dsimp only [P, PointedFlowData.atTime] at h' ⊢
    simpa only [Function.comp_def, hscale, theta] using h'

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_euclidean_model
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_euclidean_model target :: scope.openDecls } }


end EuclideanModel

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_backward_slice_normalized_shrinker_of_reducedLength_bound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
        (C : MetricConvergenceData Psi),
        (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i) ∧
        (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        (∀ x : P.M, 0 < metricScalarAt P.metric x) ∧
        (∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        ∃ f : C^∞⟮I, P.M; ℝ⟯,
          Geometry.normalizedGradientRicciSoliton P.metric f ∧
          normalizedShrinkerMass P.metric f = asymptoticReducedVolume F.S 0 p ∧
          ∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
            (fun i x => redLength F.S 0 p (Psi.map i x) (tau (phi i))) f _root_.Filter.atTop K := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  have hell (x : F.M) (t : ℝ) : redLength G.S 0 p x t = redLength F.S 0 p x t := by
    exact congrArg (fun a => a / (2 * Real.sqrt t)) (lCost_pullback_cross F.S Phi.symm 0 p x t)
  obtain ⟨P, phi, hphi, Psi, C, hcanonical, _href, hcomplete, hconnected,
    hpos, hcone, f, hsol, hmass, hpotential⟩ :=
    exists_backward_slice_normalized_shrinker_of_euclidean_model G hG p tau htau hescape q
      (fun i => (hell (q i) (tau i)).trans_le (hbase i))
  obtain ⟨L, rfl⟩ := PointedRiemannianManifold.transContinuousLinearEquiv_surjective e P
  change PointedRiemannianConvergenceMaps ((backwardSliceSequence F tau htau q).transContinuousLinearEquiv e)
    (L.transContinuousLinearEquiv e) phi at Psi
  obtain ⟨C', hcanonical', href'⟩ :=
    exists_canonicalMetricConvergenceData_of_transContinuousLinearEquiv e C hcanonical
  let Xi : L.M ≃ₘ⟮I, J⟯ L.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I L.M e
  let f' : C^∞⟮I, L.M; ℝ⟯ := f.comp Xi.toContMDiffMap
  have hcomplete' : RiemannianMetricComplete L.metric := by
    have h := RiemannianMetricComplete.pullbackCross (L.metric.transContinuousLinearEquiv e)
      Xi ⟨hcomplete⟩
    rwa [SmoothRiemannianMetric.pullback_transContinuousLinearEquiv] at h
  have hsol' : Geometry.normalizedGradientRicciSoliton L.metric f' := by
    refine ⟨hcomplete', ?_, ?_⟩
    · have h := Geometry.gradientRicciSoliton_pullbackCross hsol.2.1 Xi
      change Geometry.gradientRicciSoliton
        (Diffeomorph.pullbackMetricCross (L.metric.transContinuousLinearEquiv e) Xi) f' 1 at h
      rwa [SmoothRiemannianMetric.pullback_transContinuousLinearEquiv] at h
    · intro x
      have h := hsol.2.2 x
      change metricScalarAt (L.metric.transContinuousLinearEquiv e) x +
        Geometry.Operator.normGradSqFun (L.metric.transContinuousLinearEquiv e) f' x = f' x at h
      rwa [metricScalarAt_transContinuousLinearEquiv,
        Geometry.Operator.normGradSqFun_transContinuousLinearEquiv L.metric e f' x
          (f'.contMDiff.mdifferentiableAt (by simp))] at h
  refine ⟨L, phi, hphi, Psi.ofTransContinuousLinearEquiv e, C', hcanonical', href',
    hcomplete'.complete, hconnected, ?_, ?_, f', hsol', ?_, ?_⟩
  · intro x
    exact (metricScalarAt_transContinuousLinearEquiv L.metric e x).symm ▸ hpos x
  · intro x
    have hc : metricAlgebraicCurvatureTensorAt
        (Diffeomorph.pullbackMetricCross (L.metric.transContinuousLinearEquiv e) Xi) x ∈
          algebraicCurvatureOperatorNonnegativeCone := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff _ x).mpr
      intro m c v w
      simp_rw [metricRm04Standard_pullbackCross]
      exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (L.metric.transContinuousLinearEquiv e) x).mp (hcone x) m c _ _
    rwa [SmoothRiemannianMetric.pullback_transContinuousLinearEquiv] at hc
  · have hv : asymptoticReducedVolume G.S 0 p = asymptoticReducedVolume F.S 0 p := by
      unfold asymptoticReducedVolume
      apply iInf_congr
      intro t
      exact redVolume_transContinuousLinearEquiv F.S e 0 p t
    exact (normalizedShrinkerMass_transContinuousLinearEquiv L.metric e f').symm.trans
      (hmass.trans hv)
  · intro K hK
    apply (hpotential K hK).congr
    exact Filter.Eventually.of_forall fun i x _ => hell (Psi.map i x) (tau (phi i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_reducedLength_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_reducedLength_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_reducedLength_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_normalized_shrinker_of_reducedLength_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
