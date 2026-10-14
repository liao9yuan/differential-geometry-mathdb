import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.FixedDomain
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Immersion
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance fixedMetricLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitTopology target :: scope.openDecls } }
private local instance fixedMetricLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitCharted target :: scope.openDecls } }
private local instance fixedMetricLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitSmooth target :: scope.openDecls } }
private local instance fixedMetricLimitT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitT2 target :: scope.openDecls } }
private local instance fixedMetricLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricLimitSigma target :: scope.openDecls } }

private local instance fixedMetricApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxTopology target :: scope.openDecls } }
private local instance fixedMetricApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxCharted target :: scope.openDecls } }
private local instance fixedMetricApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxSmooth target :: scope.openDecls } }
private local instance fixedMetricApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxT2 target :: scope.openDecls } }
private local instance fixedMetricApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricApproxSigma target :: scope.openDecls } }

private local instance fixedMetricSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceTopology target :: scope.openDecls } }
private local instance fixedMetricSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceCharted target :: scope.openDecls } }
private local instance fixedMetricSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceSmooth target :: scope.openDecls } }
private local instance fixedMetricSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceT2 target :: scope.openDecls } }
private local instance fixedMetricSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricSourceSigma target :: scope.openDecls } }

private local instance fixedMetricTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetTopology target :: scope.openDecls } }
private local instance fixedMetricTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetCharted target :: scope.openDecls } }
private local instance fixedMetricTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetSmooth target :: scope.openDecls } }
private local instance fixedMetricTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetricTargetT2 target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] in
private theorem fixedMetric_canonical_inner (k : ℕ)
    (x : MetricSourceDomain (I := I) Phi k) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k)).inner x v w =
      (X.obj (subseq k)).metric.inner (Phi.map k (x : L.M))
        (mfderiv I I (Phi.map k) (x : L.M) v)
        (mfderiv I I (Phi.map k) (x : L.M) w) := by
  have hpull := Diffeomorph.pullbackMetric_inner
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k) x v w
  have hrestrict := SmoothRiemannianMetric.restrictOpen_inner
    (X.obj (subseq k)).metric (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k x)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x w)
  exact (hpull.trans hrestrict).trans (congrArg₂
    (fun V Z : E => (X.obj (subseq k)).metric.inner (Phi.map k (x : L.M)) V Z)
    (metric_source_target_diffeomorph_mfderiv Phi k x v)
    (metric_source_target_diffeomorph_mfderiv Phi k x w))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetric_canonical_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedMetric_canonical_inner target :: scope.openDecls } }

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]
  [T2Space S] [SigmaCompactSpace S]

omit [CompleteSpace E] [CompleteSpace F] [SigmaCompactSpace S] in
theorem canonicalSource_fixedDomain_pullback_eq_induced
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) :
    fixedDomainPullbackMetric e U (metricSourceOpenSubset Phi k) hU
        (canonicalSourceData Phi k).pullbackMetric =
      immersionInducedMetric (X.obj (subseq k)).metric
        (pointedMaps_restrict_isSmoothEmbedding Phi e U k hU).isImmersion := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have he : MDifferentiableAt J I e (x : S) := e.mdifferentiable (by decide) x
  have hval : MDifferentiableAt J J (Subtype.val : U → S) x :=
    (contMDiff_subtype_val (I := J) (U := U) (n := ∞)).mdifferentiable (by decide) x
  have hmap : MDifferentiableAt I I (Phi.map k) (e x) :=
    (Phi.partialDiffeomorph k).mdifferentiableAt (by decide) (hU ⟨x, x.2, rfl⟩)
  have hd (a : TangentSpace J x) :
      mfderiv J I (fun y : U => Phi.map k (e y)) x a =
        mfderiv I I (Phi.map k) (e x) (mfderiv J I e (x : S) a) := by
    have hcomp := mfderiv_comp x hmap (he.comp x hval)
    rw [mfderiv_comp x he hval, mfderiv_subtype_val] at hcomp
    exact DFunLike.congr_fun hcomp a
  have hleft := (fixedDomainPullbackMetric_inner e U (metricSourceOpenSubset Phi k) hU
    (canonicalSourceData Phi k).pullbackMetric x v w).trans
      (fixedMetric_canonical_inner Phi k ⟨e x, hU ⟨x, x.2, rfl⟩⟩
        (mfderiv J I e (x : S) v) (mfderiv J I e (x : S) w))
  have hright := (immersionInducedMetric_inner (X.obj (subseq k)).metric
    (pointedMaps_restrict_isSmoothEmbedding Phi e U k hU).isImmersion x v w).trans
      (congrArg₂ (fun V Z : E => (X.obj (subseq k)).metric.inner
        (Phi.map k (e x)) V Z) (hd v) (hd w))
  exact hleft.trans hright.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_pullback_eq_induced then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_pullback_eq_induced"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_pullback_eq_induced ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_pullback_eq_induced

theorem canonicalSource_fixedDomain_sup_eq
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) (K : Set U) (p : ℕ) :
    metricDerivNormSupOn (I := J) K p
        (immersionInducedMetric (X.obj (subseq k)).metric
          (pointedMaps_restrict_isSmoothEmbedding Phi e U k hU).isImmersion)
        ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U)
        ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U) =
      (canonicalSourceData Phi k).derivNormSupOn (I := I)
        (e '' ((Subtype.val : U → S) '' K)) p := by
  let W := metricSourceOpenSubset Phi k
  have hlimit : fixedDomainPullbackMetric e U W hU
        (canonicalSourceData Phi k).limitMetric =
      (Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U :=
    fixedDomainPullbackMetric_restrict e U W hU L.metric
  have href : fixedDomainPullbackMetric e U W hU
        (canonicalSourceData Phi k).referenceMetric =
      (Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U :=
    fixedDomainPullbackMetric_restrict e U W hU L.metric
  have himage : ((fun x : U => (⟨e x, hU ⟨x, x.2, rfl⟩⟩ : W)) '' K) =
      metricSourceCompactSet (I := I) Phi k (e '' ((Subtype.val : U → S) '' K)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, hx, Subtype.ext hy⟩
  have hsup := metricDerivNormSupOn_fixedDomainPullback e U W hU
    (canonicalSourceData Phi k).pullbackMetric (canonicalSourceData Phi k).limitMetric
    (canonicalSourceData Phi k).referenceMetric K p
  rw [himage] at hsup
  have hnorm := congrArg
    (fun gs : SmoothRiemannianMetric J U ×
        (SmoothRiemannianMetric J U × SmoothRiemannianMetric J U) =>
      metricDerivNormSupOn (I := J) K p gs.1 gs.2.1 gs.2.2)
    (congrArg₂ Prod.mk (canonicalSource_fixedDomain_pullback_eq_induced Phi e U k hU)
      (congrArg₂ Prod.mk hlimit href))
  exact hnorm.symm.trans hsup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_sup_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_sup_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_sup_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_sup_eq

theorem pointedMaps_eventually_fixedDomain_metric_close
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k : ℕ, C.domain k = canonicalSourceData Phi k)
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S)
    (Kbuffer : Set S) (hbuffer : IsCompact Kbuffer) (hUbuffer : (U : Set S) ⊆ Kbuffer)
    (K : Set U) (hK : IsCompact K) (p : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(U, (X.obj (subseq k)).M), ∃ hf : _root_.Manifold.IsSmoothEmbedding J I ∞ f,
        (∀ x : U, f x = Phi.map k (e x)) ∧
        metricDerivNormSupOn (I := J) K p
          (immersionInducedMetric (X.obj (subseq k)).metric hf.isImmersion)
          ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U)
          ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen (I := J) U) < epsilon := by
  obtain ⟨kb, hkb⟩ := Phi.source_subset (hbuffer.image e.continuous)
  have hKimage : IsCompact (e '' ((Subtype.val : U → S) '' K)) :=
    (hK.image continuous_subtype_val).image e.continuous
  obtain ⟨kc, hkc⟩ := C.converges _ hKimage p epsilon hepsilon
  refine ⟨max kb kc, fun k hk => ?_⟩
  have hU : e '' (U : Set S) ⊆ Phi.source k :=
    (_root_.Set.image_mono hUbuffer).trans (hkb k ((le_max_left kb kc).trans hk))
  let f := pointedDomainEmbedding Phi e U k hU
  have hf : _root_.Manifold.IsSmoothEmbedding J I ∞ f :=
    pointedMaps_restrict_isSmoothEmbedding Phi e U k hU
  refine ⟨f, hf, fun _ => rfl, ?_⟩
  have hclose := (hkc k ((le_max_right kb kc).trans hk)).2
  rw [hcanonical k] at hclose
  exact (canonicalSource_fixedDomain_sup_eq Phi e U k hU K p).trans_lt hclose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomain_metric_close then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomain_metric_close"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomain_metric_close ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomain_metric_close

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
