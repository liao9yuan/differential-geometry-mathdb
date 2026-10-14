import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem continuousOn_chartGramOp_gSeqExt [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ) (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M)
          (fun t ↦ gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrict X.D)
        alpha)
      (X.D.carrier ×ˢ K) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t ↦ gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrict X.D
  have hKtgt : K ⊆ (extChartAt I alpha).target := hKchart
  have hpair : ContinuousOn
      (fun p : ℝ × E ↦ (p.1, (extChartAt I alpha).symm p.2))
      (X.D.carrier ×ˢ K) := by
    exact continuousOn_fst.prodMk
      (((continuousOn_extChartAt_symm (I := I) alpha).mono hKtgt).comp
        continuousOn_snd (fun p hp ↦ hp.2))
  have hpairMem : _root_.Set.MapsTo
      (fun p : ℝ × E ↦ (p.1, (extChartAt I alpha).symm p.2))
      (X.D.carrier ×ˢ K)
      (X.D.carrier ×ˢ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hsrc' := (extChartAt I alpha).map_target (hKtgt hp.2)
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hsrc'
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E ↦
          chartGramOnE (I := I) (G.metric p.1) alpha i j p.2)
        (X.D.carrier ×ˢ K) := by
    intro i j
    simpa only [G, MetricConnectionFamily.restrict_metric, lcMetricFamily,
      chartGramOnE_def, Function.comp_def] using
      (gSeqExt_gram_cont (I := I) Φ R bf hsrc htgt k alpha i j).comp
        hpair hpairMem
  exact continuousOn_chartGramOp G alpha hentry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartGramOp_gSeqExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartGramOp_gSeqExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartGramOp_gSeqExt ``Submission.DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartGramOp_gSeqExt

theorem FlowMetricConvergenceData.tendstoUniformlyOn_chartGramOp
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn (fun k => chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M)
          (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D) alpha)
      (chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D) alpha) _root_.Filter.atTop (_root_.Set.Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let GSeq : ℕ → MetricConnectionFamilyOn (I := I) (M := P.M) X.D := fun k =>
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  apply Geometry.Curvature.tendstoUniformlyOn_chartGramOp GSeq GInf R alpha hKc hKchart
  have hKbase : IsCompact ((extChartAt I alpha).symm '' K) :=
    hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) alpha).mono hKchart)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := co.convergencePt _ hKbase 0 ε hε
  filter_upwards [_root_.Filter.eventually_ge_atTop k₀] with k hk
  intro p hp
  have h := hk₀ k hk p.1 hp.1 0 le_rfl ((extChartAt I alpha).symm p.2) ⟨p.2, hp.2, rfl⟩
  have hn : 0 ≤ metricDerivNorm 0
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) p.1)
      (co.gInf p.1) R ((extChartAt I alpha).symm p.2) := Real.sqrt_nonneg _
  simpa only [GSeq, GInf, MetricConnectionFamily.restrict_metric, lcMetricFamily,
    Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartGramOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartGramOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartGramOp ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartGramOp

theorem FlowMetricConvergenceData.continuousOn_chartGramOp [I.Boundaryless]
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K) (hcarrier : _root_.Set.Icc beta psi ⊆ X.D.carrier) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn (chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D) alpha) (_root_.Set.Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  apply (co.tendstoUniformlyOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc).continuousOn
  apply (Eventually.of_forall fun k => ?_).frequently
  exact (continuousOn_chartGramOp_gSeqExt Φ R bf hsrc htgt (co.φ k) alpha hKchart).mono
    (_root_.Set.prod_mono_left hcarrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartGramOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartGramOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartGramOp ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartGramOp

theorem FlowMetricConvergenceData.tendstoUniformly_chartGramOp
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcont : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ContinuousOn (chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D) alpha) (_root_.Set.Icc beta psi ×ˢ K))
    {Q : Type*} {tau : Q → ℝ} {u : ℕ → Q → E} {uLim : Q → E}
    (htau : ∀ q, tau q ∈ _root_.Set.Icc beta psi)
    (huK : ∀ᶠ k in _root_.Filter.atTop, ∀ q, u k q ∈ K)
    (hlimK : ∀ q, uLim q ∈ K) (hu : TendstoUniformly u uLim _root_.Filter.atTop) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformly (fun k q => chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M)
          (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D) alpha (tau q, u k q))
      (fun q => chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D) alpha (tau q, uLim q)) atTop := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hfixed := co.tendstoUniformlyOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc
  have htauSelf : TendstoUniformly (fun _ : ℕ => tau) tau atTop := by
    rw [tendstoUniformly_iff_tendsto]
    exact tendsto_diag_uniformity (tau ∘ Prod.snd) (_root_.Filter.atTop ×ˢ ⊤)
  have hpair : TendstoUniformly
      (fun k q => (tau q, u k q)) (fun q => (tau q, uLim q)) atTop :=
    fun U hU => ((htauSelf.prodMk hu) U hU).diag_of_prod
  apply hfixed.comp_tendstoUniformly
    ((isCompact_Icc.prod hKc).uniformContinuousOn_of_continuous hcont) hpair
  · filter_upwards [huK] with k hk
    exact fun q => ⟨htau q, hk q⟩
  · exact fun q => ⟨htau q, hlimK q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformly_chartGramOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformly_chartGramOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformly_chartGramOp ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformly_chartGramOp

end DifferentialGeometry.CheegerGromovCompactness
