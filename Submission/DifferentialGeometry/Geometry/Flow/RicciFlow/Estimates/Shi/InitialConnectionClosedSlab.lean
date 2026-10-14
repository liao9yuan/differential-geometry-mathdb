import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TimeIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem continuousOn_nablaKRm04NormSqIntrinsic_of_metric_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (m : ℕ) (x : M) :
    ContinuousOn (fun s => nablaKRm04NormSqIntrinsic S m s x) (_root_.Set.Icc 0 T) := by
  have hn : ContinuousOn
      (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S m p.1 p.2)
      (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ) := by
    have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (_root_.Set.Icc 0 T)
      (uniqueDiffOn_Icc hT) hgram m).continuousOn
    apply hh.congr
    intro p _
    dsimp only
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  exact hn.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, _root_.Set.mem_univ x⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.continuousOn_nablaKRm04NormSqIntrinsic_of_metric_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.continuousOn_nablaKRm04NormSqIntrinsic_of_metric_regular target :: scope.openDecls } }

private theorem continuousWithinAt_initial_connection_pairing_of_metric_regular
    (g : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (x : M) (u w v : TangentSpace I x) :
    ContinuousWithinAt
      (fun r => (g 0).inner x (CovariantDerivative.difference
        (LeviCivita (g r)) (LeviCivita (g 0)) x u w) v) (_root_.Set.Icc 0 T) 0 := by
  have hx : extChartAt I x x ∈ interior (extChartAt I x).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior
      (self_mem_chartLeviCivitaGoodSet (I := I) x)
  have hconn : ∀ i j k : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun t => chartChristoffel (g t) x i j k (extChartAt I x x))
        (𝓝[_root_.Set.Icc 0 T] 0) (𝓝 (chartChristoffel (g 0) x i j k (extChartAt I x x))) := by
    intro i j k
    have hc := (chartChristoffel_contDiffOn g (_root_.Set.Icc 0 T)
      (uniqueDiffOn_Icc hT) hgram x i j k).continuousOn
    exact (hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, hx⟩)) 0 ⟨le_rfl, hT.le⟩
  have hlim := tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel
    g (g 0) (g 0) x hconn u w v
  have hzero : CovariantDerivative.difference
      (LeviCivita (g 0)) (LeviCivita (g 0)) x u w = 0 := by
    have h := congrFun (DifferentialGeometry.PDE.DeTurck.connectionDifference_self
      (I := I) (g 0)) x
    exact congrArg (fun A : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x => A u w) h
  change _root_.Filter.Tendsto _ _ _
  simpa only [hzero, map_zero, zero_apply] using hlim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.continuousWithinAt_initial_connection_pairing_of_metric_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.continuousWithinAt_initial_connection_pairing_of_metric_regular target :: scope.openDecls } }

theorem initialConnectionDifferenceBound_of_metric_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} {B : Set M} (hT : 0 < T)
    (hcarrier : _root_.Set.Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ s ∈ _root_.Set.Icc (0 : ℝ) T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic S 0 s y ≤ K) :
    InitialConnectionDifferenceBound S T B
      (3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T))
      (nablaRmTimeIntegral S) := by
  have hn (m : ℕ) (x : M) :=
    continuousOn_nablaKRm04NormSqIntrinsic_of_metric_regular S hT hgram m x
  have hint (x : M) : IntervalIntegrable
      (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x))
      MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hT.le]
    exact (hn 1 x).sqrt
  have hspeed (x : M) (u w v : TangentSpace I x) :
      IntervalIntegrable
        (fun s => (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v)
        MeasureTheory.volume 0 T := by
    obtain ⟨s, _, hs⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hT.le) (hn 0 x)
    exact intervalIntegrable_connectionVariationSpeed_pairing_of_curvature_bound
      S hS hT.le hcarrier hregular x u w v hs (hint x)
  have hrep := connectionDifferenceTimeIntegralOn_of_initial_continuity S hS
    hcarrier hregular
    (continuousWithinAt_initial_connection_pairing_of_metric_regular
      S.base.metric hT hgram) hspeed
  apply initialConnectionDifferenceBound_of_connectionVariation S hS hT hcarrier hregular
    hcurv (Real.sqrt_nonneg _) (connectionVariationKoszulOn_connectionVariationSpeed S T)
    (nablaRicciNormBoundOn_nablaRicci S T) hrep
  intro t ht x
  exact (hint x).mono_set (by
    rw [_root_.Set.uIcc_of_le ht.1.le, _root_.Set.uIcc_of_le hT.le]
    exact _root_.Set.Icc_subset_Icc le_rfl ht.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_of_metric_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_of_metric_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_of_metric_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_of_metric_regular


theorem initialDistanceFlowLaplacianBound_of_metric_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K Ksec r₁ : ℝ} {B : Set M} (p : M)
    (hT : 0 < T) (hcarrier : _root_.Set.Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (S.base.metric q.1) x₀ q.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ s ∈ _root_.Set.Icc (0 : ℝ) T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic S 0 s y ≤ K) (hr₁ : 0 < r₁) :
    InitialDistanceFlowLaplacianBound S T p B r₁ Ksec
      ((Module.finrank ℝ E : ℝ) *
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T) *
        (2 / r₁ + Real.sqrt (-Ksec)))
      ((Module.finrank ℝ E : ℝ) *
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T) *
        (3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
          Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)))
      (nablaRmSupWeight S) := by
  have hCconn : 0 ≤ 3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
      Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T) := by
    positivity
  have hcont : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) T, ∀ y : M,
      ContinuousOn (fun s => nablaKRm04NormSqIntrinsic S 1 s y) (_root_.Set.Icc 0 t) := by
    intro t ht y
    exact (continuousOn_nablaKRm04NormSqIntrinsic_of_metric_regular S hT hgram 1 y).mono
      (_root_.Set.Icc_subset_Icc le_rfl ht.2)
  exact initialDistanceFlowLaplacianBoundOn_of_solution_nablaRmSupWeight S hS hT
    hcarrier hregular hcurv hr₁ hCconn
    (initialConnectionDifferenceBound_nablaRmSupWeight_of_nablaRmTimeIntegral
      (initialConnectionDifferenceBound_of_metric_regular S hS hT hcarrier hregular
        hgram hcurv) hCconn hcont) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialDistanceFlowLaplacianBound_of_metric_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialDistanceFlowLaplacianBound_of_metric_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialDistanceFlowLaplacianBound_of_metric_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.initialDistanceFlowLaplacianBound_of_metric_regular

end DifferentialGeometry.PDE.RicciFlow
