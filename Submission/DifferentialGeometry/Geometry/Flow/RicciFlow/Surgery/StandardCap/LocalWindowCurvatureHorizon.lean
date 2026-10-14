import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalEndpointHorizon
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowIntrinsicBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens target :: scope.openDecls } }


private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealThreeSpace : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealThreeSpace target :: scope.openDecls } }

private theorem initial_curvature_norm_le_of_metric_bound
    {D : ℝ} {J : RealTimeInterval}
    (L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J)
    (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hzero : L.base.metric 0 = g₀) (j : ℕ) (x : standardCapWindow D) {C : ℝ}
    (hb : Real.sqrt (normSq0S g₀ x (4 + j) (iterCov g₀ 4 (metricRm04 g₀) j x)) ≤ C) :
    nablaKRm04NormSqIntrinsic L j 0 x ≤ C ^ 2 := by
  rw [← curvNormSq_eq,hzero]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  exact (Real.sqrt_le_iff).mp hb |>.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initial_curvature_norm_le_of_metric_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.initial_curvature_norm_le_of_metric_bound target :: scope.openDecls } }

theorem exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
    (N : ℕ) (ρ T K : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → N+2 ≤ m → ρ < D →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        _root_.Set.Icc 0 θ ⊆ J.carrier → _root_.Set.Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (_root_.Set.Icc 0 θ ×ˢ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ j ≤ N, ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ/32 →
          nablaKRm04NormSqIntrinsic L j t x ≤ B := by
  classical
  choose A hA hinit using exists_uniform_window_curvature_derivative_bounds
  obtain ⟨B,hB,hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
    (I := ThreeModel) N T (ρ/4) K (by positivity) (fun j => (A j)^2)
    (fun _ _ _ => sq_nonneg _)
  refine ⟨B,hB,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A₀ hA₀ D m ζ w hζ hm hρD
    J θ hθ hθT hslab hreg L hL hzero hgram hcurv j hj t ht x hx
  obtain ⟨p,hp,hcompact,hcapture,hinner⟩ :=
    CanonicalStaticInsertionWitness.exists_window_intrinsic_ball_control w hζ hρ hρD
  have hcompactL : IsCompact {y : standardCapWindow D |
      riemannianEDistOf (L.base.metric 0) p y ≤ ENNReal.ofReal (ρ/4)} := by
    rwa [hzero]
  have houter (y : standardCapWindow D)
      (hy : riemannianEDistOf (L.base.metric 0) p y ≤ ENNReal.ofReal (ρ/4)) :
      ‖y.val‖ ≤ ρ := by
    rw [hzero] at hy
    exact hcapture hy
  apply hbound (standardCapWindow D) J L θ hθ hθT hL hslab hreg hgram p hcompactL
    (fun s hs y hy => hcurv s hs y (houter y hy))
    (fun k hk hkN y hy => initial_curvature_norm_le_of_metric_bound L w.windowMetric
      hzero k y (hinit k w hζ (by omega) y ((houter y hy).trans_lt hρD))) j hj t ht x
  rw [hzero]
  have hb := hinner x hx
  simpa only [div_div,show (4:ℝ)*2=8 by norm_num] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon

end DifferentialGeometry.PDE.RicciFlow.StandardCap
