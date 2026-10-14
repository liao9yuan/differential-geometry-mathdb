import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialFlowComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon

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

theorem exists_uniform_initial_standard_cap_comparison_of_local_curvature
    (D r T K ε : ℝ) (hr : 0 < r) (hfit : 64 * r < D)
    (hT : 0 < T) (hε : 0 < ε) (N : ℕ) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      N+2 ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        _root_.Set.Icc 0 θ ⊆ J.carrier → _root_.Set.Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (_root_.Set.Icc 0 θ ×ˢ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64*r →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 (_root_.Min.min η θ),
          metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
            (L.base.metric t) ((S.val.metric t).restrictOpen (standardCapWindow D))
            (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  obtain ⟨B, hB, hcurv⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      N (64 * r) T K (by positivity)
  obtain ⟨η,ε₀,hη,hηT,hε₀,hε₀half,hcompare⟩ :=
    exists_uniform_initial_standard_cap_comparison D r (2*r) T ε (by linarith)
      (by linarith) hT hε N (fun _ => Real.sqrt B)
  refine ⟨η,ε₀,hη,hηT,hε₀,hε₀half,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal
  have hjets := hcurv w (hζ.trans hε₀half) hm hfit J θ hθ hθT
    hcarrier hregular L hL hzero hgram hlocal
  apply hcompare w (by omega) hζ J θ hθ.le hθT hcarrier hregular L hL hzero hgram
  intro j hj t ht x hx
  unfold curvDerivNorm
  rw [curvNormSq_eq]
  apply Real.sqrt_le_sqrt
  apply hjets j hj t ht x
  have he : (64*r)/32 = 2*r := by ring
  rw [he]
  exact hx.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison_of_local_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison_of_local_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison_of_local_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison_of_local_curvature

end DifferentialGeometry.PDE.RicciFlow.StandardCap
