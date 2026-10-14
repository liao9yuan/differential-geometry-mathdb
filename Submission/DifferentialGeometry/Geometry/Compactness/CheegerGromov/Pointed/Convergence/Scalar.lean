import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Tensor.Metric.CompactBounds
import Mathlib.Topology.UniformSpace.UniformApproximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedScalarModelComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarModelComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarModelComplete target :: scope.openDecls } }

private local instance pointedScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarManifoldOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarManifoldOne target :: scope.openDecls } }

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedScalarLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitTopology target :: scope.openDecls } }
private local instance pointedScalarLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitCharted target :: scope.openDecls } }
private local instance pointedScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitSmooth target :: scope.openDecls } }
private local instance pointedScalarLimitT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitT2 target :: scope.openDecls } }
private local instance pointedScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarLimitSigma target :: scope.openDecls } }

private local instance pointedScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxTopology target :: scope.openDecls } }
private local instance pointedScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxCharted target :: scope.openDecls } }
private local instance pointedScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxSmooth target :: scope.openDecls } }
private local instance pointedScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxT2 target :: scope.openDecls } }
private local instance pointedScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarApproxSigma target :: scope.openDecls } }

private local instance pointedScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceTopology target :: scope.openDecls } }
private local instance pointedScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceCharted target :: scope.openDecls } }
private local instance pointedScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceSmooth target :: scope.openDecls } }
private local instance pointedScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceT2 target :: scope.openDecls } }
private local instance pointedScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarSourceSigma target :: scope.openDecls } }

private local instance pointedScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetTopology target :: scope.openDecls } }
private local instance pointedScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetCharted target :: scope.openDecls } }
private local instance pointedScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetSmooth target :: scope.openDecls } }
private local instance pointedScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetT2 target :: scope.openDecls } }
private local instance pointedScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pointedScalarTargetSigma target :: scope.openDecls } }

variable {Phi}

theorem pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence
    {K : Set L.M} (hK : IsCompact K)
    (hconv : metricSourceConvergesOn (I := I) Phi
      (CanonicalMetricCompactness.canonicalSourceData Phi) K 2) :
    TendstoUniformlyOn
      (fun k x => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      (fun x => metricScalarAt (I := I) L.metric x) _root_.Filter.atTop K := by
  obtain ⟨A, hA0, hA⟩ := Geometry.Tensor.exists_pos_bound_norm_on_compact
    L.metric (metricRicci L.metric) hK
  let n : ℝ := Module.finrank ℝ E
  let Kb : ℝ := n * A
  let B : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hKb0 : 0 ≤ Kb := mul_nonneg hn hA0.le
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hKb (x : L.M) (hx : x ∈ K) (v : TangentSpace I x) :
      |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v := by
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) L.metric x v v]
    exact (tensor02_quadForm_abs_le_normSq0S L.metric (metricRicciAt L.metric x) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA x hx) hn)
        (metric_inner_self_nonneg L.metric x v))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  let delta : ℝ := _root_.Min.min 1 (_root_.Min.min (1 / (2 * (n + 1))) (epsilon / (B + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdB : B * delta < epsilon := by
    have ht : delta ≤ epsilon / (B + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < B + 1)).mp ht
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv delta hd0
  filter_upwards [_root_.Filter.eventually_ge_atTop k0] with k hk
  intro x hx
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) hx
    exact ht.trans hsup.le
  have hKbU (v : TangentSpace I xu) :
      |ricciTensor (I := I) gU xu v v| ≤ Kb * gU.inner xu v v := by
    have hr := ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu v v
    erw [mfderiv_subtype_val_apply] at hr
    change ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v at hr
    rw [hr]
    change |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v
    exact hKb x hx v
  have hb := metricScalar_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn
    hjet hKbU
  have hlim : metricScalarAt (I := I) gU xu = metricScalarAt (I := I) L.metric x :=
    metricScalarAt_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu
  have hpull : metricScalarAt (I := I) hU xu =
      metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) := by
    calc
      _ = metricScalarAt (I := I)
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k xu) := metricScalarAt_pullback _ _ _
      _ = _ := by
        have hr := metricScalarAt_restrictOpen (X.obj (subseq k)).metric
          (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k xu)
        erw [metric_source_target_diffeomorph_apply] at hr
        exact hr
  rw [hpull, hlim] at hb
  rw [dist_comm, Real.dist_eq]
  exact hb.trans_lt hdB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence

theorem pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    {z : ℕ → L.M} {x : L.M} (hz : _root_.Filter.Tendsto z _root_.Filter.atTop (𝓝 x)) :
    _root_.Filter.Tendsto (fun n => metricScalarAt (X.obj (subseq n)).metric (Phi.map n (z n)))
      atTop (𝓝 (metricScalarAt L.metric x)) := by
  have hK := hz.isCompact_insert_range
  have hU := pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence hK (hconv _ hK)
  apply hU.tendsto_comp (metricScalar_smooth L.metric).continuous.continuousAt.continuousWithinAt
  exact tendsto_nhdsWithin_iff.mpr ⟨hz,
    Eventually.of_forall fun n => _root_.Set.mem_insert_of_mem _ (_root_.Set.mem_range_self n)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence

theorem pointedScalar_tendsto_of_inverse_tendsto
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (y : ∀ n, (X.obj (subseq n)).M) {x : L.M}
    (hy : ∀ᶠ n in _root_.Filter.atTop, y n ∈ Phi.target n)
    (hz : _root_.Filter.Tendsto (fun n => (Phi.partialDiffeomorph n).symm (y n)) _root_.Filter.atTop (𝓝 x)) :
    _root_.Filter.Tendsto (fun n => metricScalarAt (X.obj (subseq n)).metric (y n))
      atTop (𝓝 (metricScalarAt L.metric x)) := by
  have hconv (K : Set L.M) (hK : IsCompact K) :
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2 := by
    have ht := C.converges K hK 2
    have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
    rwa [hD] at ht
  have ht := pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence hconv hz
  apply ht.congr'
  filter_upwards [hy] with n hn
  change metricScalarAt (X.obj (subseq n)).metric
    (Phi.partialDiffeomorph n ((Phi.partialDiffeomorph n).symm (y n))) = _
  have hinv : Phi.partialDiffeomorph n ((Phi.partialDiffeomorph n).symm (y n)) = y n :=
    (Phi.partialDiffeomorph n).right_inv hn
  rw [hinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_inverse_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_inverse_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_inverse_tendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedScalar_tendsto_of_inverse_tendsto

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarManifoldOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarManifoldOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarManifoldOne ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarManifoldOne

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedScalarLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitTopology
local instance pointedScalarLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitCharted
local instance pointedScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSmooth
local instance pointedScalarLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitT2
local instance pointedScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarLimitSigma

local instance pointedScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxTopology
local instance pointedScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxCharted
local instance pointedScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSmooth
local instance pointedScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxT2
local instance pointedScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarApproxSigma

local instance pointedScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceTopology
local instance pointedScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceCharted
local instance pointedScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSmooth
local instance pointedScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceT2
local instance pointedScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarSourceSigma

local instance pointedScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetTopology
local instance pointedScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetCharted
local instance pointedScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSmooth
local instance pointedScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetT2
local instance pointedScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalarTargetSigma

variable {Phi}

theorem pointedScalar_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  let n : ℝ := Module.finrank ℝ E
  let Kb : ℝ := n * Real.sqrt
    (normSq0S (I := I) L.metric x 2 (metricRicciAt (I := I) L.metric x))
  let B : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hKb0 : 0 ≤ Kb := mul_nonneg hn (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hKb (v : TangentSpace I x) :
      |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v := by
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) L.metric x v v]
    exact tensor02_quadForm_abs_le_normSq0S L.metric (metricRicciAt (I := I) L.metric x) v
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let delta : ℝ := _root_.Min.min 1 (_root_.Min.min (1 / (2 * (n + 1))) (epsilon / (B + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdB : B * delta < epsilon := by
    have ht : delta ≤ epsilon / (B + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < B + 1)).mp ht
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton delta hd0
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource (Set.mem_singleton x)⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k {x}) :=
    metric_source_compact_set_is_compact (I := I) Phi k isCompact_singleton hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k {x}) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) (Set.mem_singleton x)
    exact ht.trans hsup.le
  have hKbU (v : TangentSpace I xu) :
      |ricciTensor (I := I) gU xu v v| ≤ Kb * gU.inner xu v v := by
    have hr := DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu v v
    erw [mfderiv_subtype_val_apply] at hr
    change ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v at hr
    rw [hr]
    change |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v
    exact hKb v
  have hb := metricScalar_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn
    hjet hKbU
  have hlim : metricScalarAt (I := I) gU xu = metricScalarAt (I := I) L.metric x :=
    metricScalarAt_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu
  have hpull : metricScalarAt (I := I) hU xu =
      metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) := by
    calc
      _ = metricScalarAt (I := I)
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k xu) := metricScalarAt_pullback _ _ _
      _ = _ := by
        have hr := metricScalarAt_restrictOpen (X.obj (subseq k)).metric
          (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k xu)
        erw [metric_source_target_diffeomorph_apply] at hr
        exact hr
  rw [hpull, hlim] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hdB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence

theorem pointedScalar_tendsto_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  apply pointedScalar_tendsto_of_canonical_metric_convergence
  intro K hK
  have ht := C.converges K hK 2
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hD] at ht
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains

theorem pointedScalar_base_eq_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    {c : ℝ}
    (hbase : ∀ k, metricScalarAt (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint = c) :
    metricScalarAt (I := I) L.metric L.basepoint = c := by
  have hc := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical L.basepoint
  have heq : (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric
      (Phi.map k L.basepoint)) = fun _ : ℕ => c := by
    funext k
    have hmap : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint :=
      Phi.basepoint_map k
    rw [hmap]
    exact hbase k
  rw [heq] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains

theorem scalar_base_eq_in_canonicalMetricCompactness
    (C : CanonicalMetricCompactness (I := I) X) {c : ℝ}
    (hbase : ∀ k,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let _ : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let _ : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let _ : T2Space (X.obj k).M := (X.obj k).t2
      metricScalarAt (I := I) (X.obj k).metric (X.obj k).basepoint = c) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = c :=
  pointedScalar_base_eq_of_metricCG_canonical_domains C.compactness.convergence.metrics
    C.domain_eq_canonical (fun k => hbase (C.compactness.subseq k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_base_eq_in_canonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_base_eq_in_canonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_base_eq_in_canonicalMetricCompactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_base_eq_in_canonicalMetricCompactness


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedCompactScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarManifoldOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarManifoldOne target :: scope.openDecls } }

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedCompactScalarLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitTopology target :: scope.openDecls } }
private local instance pointedCompactScalarLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitCharted target :: scope.openDecls } }
private local instance pointedCompactScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitSmooth target :: scope.openDecls } }
private local instance pointedCompactScalarLimitT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitT2 target :: scope.openDecls } }
private local instance pointedCompactScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarLimitSigma target :: scope.openDecls } }

private local instance pointedCompactScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxTopology target :: scope.openDecls } }
private local instance pointedCompactScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxCharted target :: scope.openDecls } }
private local instance pointedCompactScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxSmooth target :: scope.openDecls } }
private local instance pointedCompactScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxT2 target :: scope.openDecls } }
private local instance pointedCompactScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarApproxSigma target :: scope.openDecls } }

private local instance pointedCompactScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceTopology target :: scope.openDecls } }
private local instance pointedCompactScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceCharted target :: scope.openDecls } }
private local instance pointedCompactScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceSmooth target :: scope.openDecls } }
private local instance pointedCompactScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceT2 target :: scope.openDecls } }
private local instance pointedCompactScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarSourceSigma target :: scope.openDecls } }

private local instance pointedCompactScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetTopology target :: scope.openDecls } }
private local instance pointedCompactScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetCharted target :: scope.openDecls } }
private local instance pointedCompactScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetSmooth target :: scope.openDecls } }
private local instance pointedCompactScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetT2 target :: scope.openDecls } }
private local instance pointedCompactScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactScalarTargetSigma target :: scope.openDecls } }

variable {Phi}

theorem pointedScalar_uniform_on_compact_of_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Phi.source k ∧ ∀ x ∈ K,
        |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| < epsilon := by
  have hconv := C.converges K hK 2
  have hdomain : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi :=
    funext hcanonical
  rw [hdomain] at hconv
  have hU := CheegerGromovCompactness.pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence
    hK hconv
  intro epsilon hepsilon
  have he := Metric.tendstoUniformlyOn_iff.mp hU epsilon hepsilon
  obtain ⟨Ns, hNs⟩ := Phi.source_subset hK
  obtain ⟨Ne, hNe⟩ := Filter.eventually_atTop.mp he
  refine ⟨max Ns Ne, fun k hk => ⟨hNs k ((le_max_left _ _).trans hk), ?_⟩⟩
  intro x hx
  have hd := hNe k ((le_max_right _ _).trans hk) x hx
  simpa only [Real.dist_eq, abs_sub_comm] using hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains

theorem exists_pointed_scalar_bound_on_compact
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in _root_.Filter.atTop, K ⊆ Phi.source k ∧
      ∀ x ∈ K, |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| ≤ B := by
  obtain ⟨R, hR⟩ := (hK.image (metricScalar_smooth (I := I) L.metric).continuous.abs).bddAbove
  obtain ⟨k0, hk0⟩ := pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 zero_lt_one
  refine ⟨max R 0 + 1, by positivity, Filter.eventually_atTop.2 ⟨k0, fun k hk => ?_⟩⟩
  refine ⟨(hk0 k hk).1, fun x hx => ?_⟩
  have herr := (hk0 k hk).2 x hx
  have hlim : |metricScalarAt (I := I) L.metric x| ≤ _root_.Max.max R 0 :=
    (hR ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  calc
    |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| =
        |(metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x) + metricScalarAt (I := I) L.metric x| := by
      rw [sub_add_cancel]
    _ ≤ |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| + |metricScalarAt (I := I) L.metric x| :=
      abs_add_le _ _
    _ ≤ _root_.Max.max R 0 + 1 := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_positive_pointed_scalar_bounds_on_compact
    (Phi : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (K : Set L.M) (hK : IsCompact K) (hpositive : ∀ x ∈ K, 0 < metricScalarAt L.metric x) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ c ≤ B ∧ ∀ᶠ i in _root_.Filter.atTop,
      K ⊆ Phi.source i ∧ ∀ x ∈ K,
        c ≤ metricScalarAt (X.obj (subseq i)).metric (Phi.map i x) ∧
          metricScalarAt (X.obj (subseq i)).metric (Phi.map i x) ≤ B := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · subst K
    exact ⟨1,1,zero_lt_one,zero_lt_one,le_rfl,Eventually.of_forall fun _ => by simp⟩
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hKne (metricScalar_smooth L.metric).continuous.continuousOn
  let c := metricScalarAt L.metric x / 2
  have hc : 0 < c := half_pos (hpositive x hx)
  obtain ⟨B,hB,hupper⟩ := exists_pointed_scalar_bound_on_compact C hcanonical K hK
  obtain ⟨j,hj⟩ := pointedScalar_uniform_on_compact_of_canonical_domains C hcanonical K hK c hc
  refine ⟨c,_root_.Max.max c B,hc,lt_max_of_lt_right hB,le_max_left _ _,?_⟩
  filter_upwards [hupper,_root_.Filter.eventually_ge_atTop j] with i hi hji
  refine ⟨hi.1,?_⟩
  intro y hy
  have herr := (abs_lt.mp ((hj i hji).2 y hy)).1
  have hlow : metricScalarAt L.metric x ≤ metricScalarAt L.metric y := hmin hy
  refine ⟨?_,(le_abs_self _).trans ((hi.2 y hy).trans (le_max_right _ _))⟩
  dsimp only [c] at *
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
