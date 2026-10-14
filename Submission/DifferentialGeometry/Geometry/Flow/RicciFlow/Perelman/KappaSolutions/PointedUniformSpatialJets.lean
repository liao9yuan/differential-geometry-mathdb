import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedChartJetBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedUniformMetricTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.UniformCoordinateJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance spatialUniformTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformTopology target :: scope.openDecls } }
private local instance spatialUniformCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformCharted target :: scope.openDecls } }
private local instance spatialUniformSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformSmooth target :: scope.openDecls } }
private local instance spatialUniformC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformC1 target :: scope.openDecls } }
private local instance spatialUniformT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformT2 target :: scope.openDecls } }
private local instance spatialUniformSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformSigma target :: scope.openDecls } }

private local instance spatialUniformMetricTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricTopology target :: scope.openDecls } }
private local instance spatialUniformMetricCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricCharted target :: scope.openDecls } }
private local instance spatialUniformMetricSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialUniformMetricSmooth target :: scope.openDecls } }

variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
  (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
  {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
  (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
  (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
    ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
    ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
      (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
  {a : ℝ}
  (hconv : ∀ t ∈ Icc a 0,
    ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
      ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
        (I := I) (Phi.atTime (L := L) t) k)

include hsource hG hconv


theorem pointed_extension_inner_uniform_on_closed_time
    (ha : a ≤ 0) (x : L.M) (v w : TangentSpace I x) :
    TendstoUniformlyOn (fun i t => (G i t).inner x v w)
      (fun t => (L.S.base.metric t).inner x v w) _root_.Filter.atTop (_root_.Set.Icc a 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let S : ℝ := (L.S.base.metric 0).inner x (v + w) (v + w) +
    (L.S.base.metric 0).inner x v v + (L.S.base.metric 0).inner x w w
  have hnonneg (z : TangentSpace I x) : 0 ≤ (L.S.base.metric 0).inner x z z := by
    by_cases hz : z = 0
    · subst z
      simp
    · exact ((L.S.base.metric 0).pos x z hz).le
  have hS : 0 ≤ S := add_nonneg (add_nonneg (hnonneg (v + w)) (hnonneg v)) (hnonneg w)
  let δ : ℝ := ε / (S + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : δ * S < ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < S + 1)]
    nlinarith
  filter_upwards [pointed_metric_quadratic_uniform_on_closed_time
    Phi hsource ha {x} isCompact_singleton hconv δ hδ, hG {x} isCompact_singleton]
    with i hi hGi
  obtain ⟨U, _hU, hKU, _hUsource, hpair⟩ := hGi
  intro t ht
  have hquad (z : TangentSpace I x) :
      |(G i t).inner x z z - (L.S.base.metric t).inner x z z| ≤
        δ * (L.S.base.metric 0).inner x z z := by
    rw [hpair t x (hKU (_root_.Set.mem_singleton x)) z z]
    exact hi.2 t ht x (_root_.Set.mem_singleton x) z
  have huv := abs_le.mp (hquad (v + w))
  have hv := abs_le.mp (hquad v)
  have hw := abs_le.mp (hquad w)
  rw [metric_add_self (G i t) x v w, metric_add_self (L.S.base.metric t) x v w] at huv
  have hbound : |(G i t).inner x v w - (L.S.base.metric t).inner x v w| ≤ δ * S := by
    rw [abs_le]
    dsimp only [S]
    constructor <;> nlinarith [mul_nonneg hδ.le hS]
  simpa only [Real.dist_eq, abs_sub_comm] using hbound.trans_lt hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_extension_inner_uniform_on_closed_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_extension_inner_uniform_on_closed_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_extension_inner_uniform_on_closed_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_extension_inner_uniform_on_closed_time


theorem pointed_spatial_jets_uniform_on_closed_time
    (hdim : Module.finrank ℝ E = 3)
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) 0))
    (ha : a < 0) (A : ℝ) (hA : 0 ≤ A) (x₀ : L.M)
    (j k : Fin (Module.finrank ℝ E))
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt I x₀).target)
    (hball : ∀ y ∈ U, (extChartAt I x₀).symm y ∈
      riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a 0, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G i t) x₀ j k) y -
        iteratedFDeriv ℝ r (chartGramOnE (I := I) (L.S.base.metric t) x₀ j k) y‖ ≤ ε := by
  obtain ⟨C0, hc0⟩ := hconv 0 ⟨ha.le, le_rfl⟩
  obtain ⟨Ca, hca⟩ := hconv a ⟨le_rfl, ha.le⟩
  apply uniform_spatial_jets_on_compact_time_of_local_bounds hU _root_.CompactIccSpace.isCompact_Icc
    (fun i t => chartGramOnE (I := I) (G i t) x₀ j k)
    (fun t => chartGramOnE (I := I) (L.S.base.metric t) x₀ j k)
    (fun i t _ => (chartGramOnE_contDiffOn (I := I) (G i t) x₀ j k).mono hchart)
    (fun t _ => (chartGramOnE_contDiffOn (I := I) (L.S.base.metric t) x₀ j k).mono hchart)
    ?_ ?_ ?_ hK hKU r
  · intro y _hy
    change ContinuousOn (fun t => (L.S.base.metric t).inner ((extChartAt I x₀).symm y)
      (chartBasisVecFiber (I := I) x₀ j ((extChartAt I x₀).symm y))
      (chartBasisVecFiber (I := I) x₀ k ((extChartAt I x₀).symm y))) (_root_.Set.Icc a 0)
    apply (L.isSolution.smoothMetric.coeff_cont _ _ _).mono
    intro t ht
    rw [(hsource 0).carrier_eq]
    exact ht.2
  · intro q K' hK' hK'U
    let Kc : Set L.M := (extChartAt I x₀).symm '' K'
    have hKc : IsCompact Kc := hK'.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) x₀).mono (hK'U.trans hchart))
    have hKcChart : Kc ⊆ (chartAt H x₀).source := by
      rintro _ ⟨y, hy, rfl⟩
      have hs := (extChartAt I x₀).map_target (hchart (hK'U hy))
      rwa [extChartAt_source_eq_chartAt_source] at hs
    have hKcBall : Kc ⊆ riemannianClosedBallOf (I := I)
        (L.S.base.metric 0) L.basepoint A := by
      rintro _ ⟨y, hy, rfl⟩
      exact hball y (hK'U hy)
    obtain ⟨B, _hB, hbdd⟩ := exists_pointed_uniform_chart_jet_bound
      hdim Phi hsource hnormalized hcomplete G hG ha C0 hc0 Ca hca
      A hA x₀ hKc hKcChart hKcBall q
    refine ⟨B, ?_⟩
    filter_upwards [hbdd] with i hi
    intro t ht y hy
    have h := hi t ht ((extChartAt I x₀).symm y) (_root_.Set.mem_image_of_mem _ hy) j k
    simpa only [(extChartAt I x₀).right_inv (hchart (hK'U hy))] using h
  · intro y _hy
    exact pointed_extension_inner_uniform_on_closed_time Phi hsource G hG hconv ha.le
      ((extChartAt I x₀).symm y)
      (chartBasisVecFiber (I := I) x₀ j ((extChartAt I x₀).symm y))
      (chartBasisVecFiber (I := I) x₀ k ((extChartAt I x₀).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_spatial_jets_uniform_on_closed_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_spatial_jets_uniform_on_closed_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_spatial_jets_uniform_on_closed_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_spatial_jets_uniform_on_closed_time

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
